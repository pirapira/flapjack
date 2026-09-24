import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake semantic `Seq` result

The source oracle is `scripts/hol-probes/pan_sem_seq_e2e_probe.out`, generated
from `panSemScript.sml:615-618`. It pins five `Seq` outcomes against the
production evaluator:

* two `Skip`s complete normally at the same clock with locals preserved;
* a `Break` first command short-circuits (the second command is not run);
* a `Continue` first command short-circuits;
* a rejected first command (shape mismatch) yields `SOME Error` at the same
  clock;
* the clock is clamped to the decremented value after a `Tick` first command.
-/

namespace Flapjack.Test.PanSemSeqParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def seqState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
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

def seqEvaluate (clock : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (seqState clock) program

def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

def isNormalAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.normal _ _ _ _), n), _) => n == clock
  | _ => false

def isBrokeAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.broke _ _ _ _), n), _) => n == clock
  | _ => false

def isContinuedAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.continued _ _ _ _), n), _) => n == clock
  | _ => false

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def normalSeq : Prog Word64 := .seq .skip .skip

def breakSeq : Prog Word64 :=
  .seq .break (.assign .local "x" (.const (BitVec.ofNat 64 9)))

def continueSeq : Prog Word64 := .seq .continue .skip

def errorSeq : Prog Word64 :=
  .seq (.dec "x" (.named "Other") (.const (BitVec.ofNat 64 7)) .skip) .skip

def tickSeq : Prog Word64 := .seq .tick .skip

def seqNormalGuard : Bool :=
  isNormalAt 5 (seqEvaluate 5 normalSeq) &&
    (match seqEvaluate 5 normalSeq with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def seqBreakGuard : Bool :=
  isBrokeAt 5 (seqEvaluate 5 breakSeq) &&
    (match seqEvaluate 5 breakSeq with
     | some ((.control (.broke locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def seqContinueGuard : Bool := isContinuedAt 5 (seqEvaluate 5 continueSeq)

def seqErrorGuard : Bool :=
  isErrorAt 5 (seqEvaluate 5 errorSeq) &&
    (match seqEvaluate 5 errorSeq with
     | some ((.control (.error locals _ _ _), n), _) => n == 5 && isWordOption 3 (locals "x")
     | _ => false)

def seqTickGuard : Bool := isNormalAt 4 (seqEvaluate 5 tickSeq)

def seqGuard : Bool :=
  seqNormalGuard && seqBreakGuard && seqContinueGuard && seqErrorGuard && seqTickGuard

#guard seqGuard

example : seqEvaluate 5 normalSeq = seqEvaluate 5 (.seq .skip .skip) := rfl

def runChecks : IO Bool := do
  if seqNormalGuard then
    IO.println "PASS panSem Seq normal pair completes with locals preserved"
  else IO.println "FAIL panSem Seq normal pair completes with locals preserved"
  if seqBreakGuard then
    IO.println "PASS panSem Seq Break short-circuits with unchanged state"
  else IO.println "FAIL panSem Seq Break short-circuits with unchanged state"
  if seqContinueGuard then
    IO.println "PASS panSem Seq Continue short-circuits"
  else IO.println "FAIL panSem Seq Continue short-circuits"
  if seqErrorGuard then
    IO.println "PASS panSem Seq rejected first command yields Error"
  else IO.println "FAIL panSem Seq rejected first command yields Error"
  if seqTickGuard then
    IO.println "PASS panSem Seq clamps clock after Tick"
  else IO.println "FAIL panSem Seq clamps clock after Tick"
  pure seqGuard

end Flapjack.Test.PanSemSeqParity
