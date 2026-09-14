import Flapjack.LoopFindCode

/-!
Faithful Loop state and result boundary.

This mirrors the original CakeML Pancake `loopSem` state and result datatypes
(`cakeml/pancake/semantics/loopSemScript.sml:13-37`) with an explicit clock and
code environment, word-valued results, and control-result propagation.  It is
independent of the legacy `Flapjack.LoopState`/`LoopResult` model so that the
existing proofs can migrate incrementally.
-/

namespace Flapjack

/-- Original `loopSem` result datatype; `α` is the FFI event type. -/
inductive LoopMachineResult (α : Type) where
  | result (values : List LoopWordLoc)
  | except (value : LoopWordLoc)
  | break (count : Nat)
  | continue (count : Nat)
  | timeOut
  | finalFfi (event : α)
  | error
  deriving DecidableEq, Repr

/-- Original `loopSem` state datatype; `α` is the address and FFI event type. -/
structure LoopMachineState (α : Type) where
  locals : Nat → Option LoopWordLoc
  globals : Nat → Option LoopWordLoc
  memory : α → Option LoopWordLoc
  mdomain : α → Bool
  shMdomain : α → Bool
  clock : Nat
  code : LoopCode LoopWordLoc
  be : Bool
  ffi : α
  baseAddr : α
  topAddr : α

/--
Faithful port of `exit_loop` (`loopSemScript.sml:272-276`): `Break n` and
`Continue n` decrement their counter with truncating subtraction, and every
other result is unchanged.
-/
def exitLoop : Option (LoopMachineResult α) → Option (LoopMachineResult α)
  | none => none
  | some (.break count) => some (.break (count - 1))
  | some (.continue count) => some (.continue (count - 1))
  | some other => some other

/-- Faithful port of `dec_clock` (`loopSemScript.sml:42`). -/
def decrementLoopClock (state : LoopMachineState α) : LoopMachineState α :=
  { state with clock := state.clock - 1 }

/-! Exact executable counterpart of CakeML's `cut_state_def`
    (`loopSemScript.sml:182-186`).  The source checks that every live local is
    present, then intersects the local map with the live set while preserving
    every other machine-state component. -/
def loopLiveLocalsPresent (locals : Nat → Option LoopWordLoc) : List Nat → Bool
  | [] => true
  | name :: names => (locals name).isSome && loopLiveLocalsPresent locals names

def loopRestrictLocals (locals : Nat → Option LoopWordLoc) (live : List Nat) :
    Nat → Option LoopWordLoc :=
  fun name => if name ∈ live then locals name else none

def cutLoopState (live : List Nat) (state : LoopMachineState α) :
    Option (LoopMachineState α) :=
  if loopLiveLocalsPresent state.locals live then
    some { state with locals := loopRestrictLocals state.locals live }
  else none

/-! Exact executable counterpart of CakeML's `cut_res_def`
    (`loopSemScript.sml:189-197`). -/
def cutLoopResult (live : List Nat)
    (step : Option (LoopMachineResult α) × LoopMachineState α) :
    Option (LoopMachineResult α) × LoopMachineState α :=
  let (result, state) := step
  if result.isSome then
    (result, state)
  else
    match cutLoopState live state with
    | none => (some .error, state)
    | some state =>
        if state.clock = 0 then
          (some .timeOut, { state with locals := fun _ => none })
        else
          (none, decrementLoopClock state)

theorem exitLoop_none {α : Type} : exitLoop (none : Option (LoopMachineResult α)) = none := rfl

theorem exitLoop_break {α : Type} (count : Nat) :
    exitLoop (α := α) (some (.break count)) = some (.break (count - 1)) := rfl

theorem exitLoop_continue {α : Type} (count : Nat) :
    exitLoop (α := α) (some (.continue count)) = some (.continue (count - 1)) := rfl

end Flapjack
