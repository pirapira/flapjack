import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `Tick` equation

The source oracle is `scripts/hol-probes/pan_sem_tick_e2e_probe.out`, generated
from `panSemScript.sml:653-655` (`Tick`), `:441-443` (`dec_clock_def`), and
`empty_locals_def`. It pins the zero-clock `SOME TimeOut` branch with cleared
locals and the positive-clock `NONE` branch with the clock decremented and
locals preserved.

`panSemEvaluateCodeStateWithPostState_tick` is the untagged production
equation; the reduced result representation means the statement is not HOL's
`(prog_result, state)` pair, so it carries no `@[hol]` tag.
-/

namespace Flapjack.Test.PanSemTickParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

abbrev TickResult :=
  Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))

def tickState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
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

def tickEvaluate (clock : Nat) : TickResult :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (tickState clock) (.tick : Prog Word64)

def tickZeroPost : PanSemState Word64 (FfiState Unit) :=
  { (tickState 0) with locals := fun _ => none }

def tickZeroExpected : TickResult :=
  some ((.timeout (fun _ => none) (tickState 0).globals (tickState 0).memory
      (tickState 0).ffi, 0), tickZeroPost)

def tickSuccPost : PanSemState Word64 (FfiState Unit) :=
  { (tickState 5) with clock := 4 }

def tickSuccOutcome : PanValueFfiClockResult Word64 Unit :=
  (.control (.normal (tickState 5).locals (tickState 5).globals
      (tickState 5).memory (tickState 5).ffi), 4)

def tickSuccExpected : TickResult :=
  some (tickSuccOutcome, tickSuccPost)

theorem tickZero_eq : tickEvaluate 0 = tickZeroExpected := by
  unfold tickEvaluate tickZeroExpected
  rw [panSemEvaluateCodeStateWithPostState_tick]
  simp [tickState, tickZeroPost]

theorem tickSucc_eq : tickEvaluate 5 = tickSuccExpected := by
  unfold tickEvaluate tickSuccExpected
  rw [panSemEvaluateCodeStateWithPostState_tick]
  simp [tickState, tickSuccPost, tickSuccOutcome]

def isWord (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

def tickZeroGuard : Bool :=
  match tickEvaluate 0 with
  | some ((.timeout locals _ _ _, 0), post) =>
      locals "x" = none && post.locals "x" = none && post.clock = 0
  | _ => false

def tickSuccGuard : Bool :=
  match tickEvaluate 5 with
  | some ((.control (.normal locals _ _ _), 4), post) =>
      isWord 7 (locals "x") && isWord 7 (post.locals "x") && post.clock = 4
  | _ => false

#guard tickZeroGuard
#guard tickSuccGuard

def runChecks : IO Bool := do
  if tickZeroGuard then IO.println "PASS panSem Tick zero-clock timeout clears locals"
  else IO.println "FAIL panSem Tick zero-clock timeout clears locals"
  if tickSuccGuard then IO.println "PASS panSem Tick positive clock decrements and preserves locals"
  else IO.println "FAIL panSem Tick positive clock decrements and preserves locals"
  pure (tickZeroGuard && tickSuccGuard)

end Flapjack.Test.PanSemTickParity
