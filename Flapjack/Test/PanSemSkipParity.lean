import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `Skip` equation

The source oracle is `scripts/hol-probes/pan_sem_skip_e2e_probe.out`, generated
from `panSemScript.sml:557` (`Skip`). It pins the normal (`NONE`) result with
the whole state, including the clock and locals, carried verbatim.

`panSemEvaluateCodeStateWithPostState_skip` is the untagged production equation;
the reduced result representation means the statement is not HOL's
`(prog_result, state)` pair, so it carries no `@[hol]` tag.
-/

namespace Flapjack.Test.PanSemSkipParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

abbrev SkipResult :=
  Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))

def skipState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 7)) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def skipEvaluate (clock : Nat) : SkipResult :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (skipState clock) (.skip : Prog Word64)

def skipOutcome : PanValueFfiClockResult Word64 Unit :=
  (.control (.normal (skipState 5).locals (skipState 5).globals
      (skipState 5).memory (skipState 5).ffi), 5)

def skipExpected : SkipResult :=
  some (skipOutcome, skipState 5)

theorem skip_eq : skipEvaluate 5 = skipExpected := by
  unfold skipEvaluate skipExpected
  rw [panSemEvaluateCodeStateWithPostState_skip]
  simp [skipState, skipOutcome]

def isWord (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

def skipGuard : Bool :=
  match skipEvaluate 5 with
  | some ((.control (.normal locals _ _ _), 5), post) =>
      isWord 7 (locals "x") && isWord 7 (post.locals "x") && post.clock = 5
  | _ => false

#guard skipGuard

theorem skipGuard_true : skipGuard = true := by native_decide

def runChecks : IO Bool := do
  if skipGuard then IO.println "PASS panSem Skip normal result preserves clock and locals"
  else IO.println "FAIL panSem Skip normal result preserves clock and locals"
  pure skipGuard

end Flapjack.Test.PanSemSkipParity
