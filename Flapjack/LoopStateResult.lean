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

theorem exitLoop_none {α : Type} : exitLoop (none : Option (LoopMachineResult α)) = none := rfl

theorem exitLoop_break {α : Type} (count : Nat) :
    exitLoop (α := α) (some (.break count)) = some (.break (count - 1)) := rfl

theorem exitLoop_continue {α : Type} (count : Nat) :
    exitLoop (α := α) (some (.continue count)) = some (.continue (count - 1)) := rfl

end Flapjack