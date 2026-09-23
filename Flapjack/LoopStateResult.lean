import Flapjack.LoopFindCode
import Flapjack.Ffi

/-!
Faithful Loop state and result boundary.

This mirrors the original CakeML Pancake `loopSem` state and result datatypes
(`cakeml/pancake/semantics/loopSemScript.sml:13-37`) with an explicit clock and
code environment, word-valued results, and control-result propagation.  It is
independent of the legacy `Flapjack.LoopState`/`LoopResult` model so that the
existing proofs can migrate incrementally.

As in HOL, the state is parameterized by the word type `W` (used for locals,
globals, memory addresses, and the base/top addresses) and separately by the
oracle host-state type `F`, so that `ffi : FfiState F` is the source
`'ffi ffi_state` (`ffiScript.sml:47-52`).  The result datatype is parameterized
by `W` only: its `FinalFFI` constructor carries the fixed `final_event`
(`ffiScript.sml:43`), which is independent of the FFI state type.
-/

namespace Flapjack

/-- Original `loopSem` result datatype (`loopSemScript.sml:30-37`); result
    values use the word type `W`, while `finalFfi` carries the fixed
    `final_event` (`ffiScript.sml:43`), independent of the FFI state type. -/
inductive LoopMachineResult (W : Type := Nat) where
  | result (values : List (LoopValue W))
  | except (value : LoopValue W)
  | break (count : Nat)
  | continue (count : Nat)
  | timeOut
  | finalFfi (event : FfiFinalEvent)
  | error
  deriving DecidableEq, Repr

/-- Original `loopSem` state datatype (`loopSemScript.sml:13-27`); `W` is the
    word/address type and `F` the oracle host-state type, so `ffi : FfiState F`
    is the source `'ffi ffi_state`. -/
structure LoopMachineState (W : Type := Nat) (F : Type := Nat) where
  locals : Nat → Option (LoopValue W)
  globals : BitVec 5 → Option (LoopValue W)
  memory : W → Option (LoopValue W)
  mdomain : W → Bool
  shMdomain : W → Bool
  clock : Nat
  code : LoopCode W
  be : Bool
  ffi : FfiState F
  baseAddr : W
  topAddr : W

/-- A canonical FFI state with a diverging oracle, for building machine states
    in tests and probe harnesses. -/
def trivialFfiState (F : Type) (state : F) : FfiState F :=
  { oracle := fun _ _ _ _ => .final .failed, state := state, ioEvents := [] }

/--
Faithful port of `exit_loop` (`loopSemScript.sml:272-276`): `Break n` and
`Continue n` decrement their counter with truncating subtraction, and every
other result is unchanged.
-/
def exitLoop : Option (LoopMachineResult W) → Option (LoopMachineResult W)
  | none => none
  | some (.break count) => some (.break (count - 1))
  | some (.continue count) => some (.continue (count - 1))
  | some other => some other

/-- Faithful port of `dec_clock` (`loopSemScript.sml:42`). -/
def decrementLoopClock (state : LoopMachineState W F) : LoopMachineState W F :=
  { state with clock := state.clock - 1 }

/-! Exact executable counterpart of CakeML's `cut_state_def`
    (`loopSemScript.sml:182-186`).  The source checks that every live local is
    present, then intersects the local map with the live set while preserving
    every other machine-state component. -/
def loopLiveLocalsPresent (locals : Nat → Option (LoopValue W)) : List Nat → Bool
  | [] => true
  | name :: names => (locals name).isSome && loopLiveLocalsPresent locals names

def loopRestrictLocals (locals : Nat → Option (LoopValue W)) (live : List Nat) :
    Nat → Option (LoopValue W) :=
  fun name => if name ∈ live then locals name else none

def cutLoopState (live : List Nat) (state : LoopMachineState W F) :
    Option (LoopMachineState W F) :=
  if loopLiveLocalsPresent state.locals live then
    some { state with locals := loopRestrictLocals state.locals live }
  else none

/-! Exact executable counterpart of CakeML's `cut_res_def`
    (`loopSemScript.sml:189-197`). -/
def cutLoopResult (live : List Nat)
    (step : Option (LoopMachineResult W) × LoopMachineState W F) :
    Option (LoopMachineResult W) × LoopMachineState W F :=
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

theorem exitLoop_none {W : Type} :
    exitLoop (none : Option (LoopMachineResult W)) = none := rfl

theorem exitLoop_break {W : Type} (count : Nat) :
    exitLoop (some (.break count) : Option (LoopMachineResult W)) =
      some (.break (count - 1)) := rfl

theorem exitLoop_continue {W : Type} (count : Nat) :
    exitLoop (some (.continue count) : Option (LoopMachineResult W)) =
      some (.continue (count - 1)) := rfl

end Flapjack
