import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake semantic `Return` and `Raise` failures

The source oracle is `scripts/hol-probes/pan_sem_return_raise_error_probe.out`,
generated from `panSemScript.sml` (see lines 633-650). It pins:

* `Return e` with a failing expression, and `Return e` with an oversized
  payload, both to `SOME Error`; the guards check the clock, local `x`,
  representative empty global and memory lookups, and the test FFI state;
* a well-sized `Return e` to `SOME (Return v)` with cleared locals and payload
  `[ValWord 7w]`;
* `Raise eid e` with a missing declared shape, a failing expression, an
  oversized payload, and a mismatched shape, all to `SOME Error` with the
  unchanged state;
* a well-matched `Raise eid e` to `SOME (Exception eid v)` with cleared locals,
  exception identifier `E`, and payload `ValWord 7w`.
-/

namespace Flapjack.Test.PanSemReturnRaiseErrorParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def returnRaiseState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
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

def returnRaiseEvaluate (clock : Nat) (program : Prog Word64)
    (contracts : Option PanValueCallContracts := none) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (returnRaiseState clock) program
    (contracts := contracts)

def contractsWith (exceptionShapes : InfoMap Shape) : PanValueCallContracts :=
  { returnShapes := [], exceptionShapes := exceptionShapes }

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def isMissingLocal (value : Option (PanValue Word64)) : Bool := value.isNone

def isWordValue (expected : Nat) (value : PanValue Word64) : Bool :=
  match value with
  | .word word => word == BitVec.ofNat 64 expected
  | _ => false

def isWordList (expected : Nat) : List (PanValue Word64) → Bool
  | [.word word] => word == BitVec.ofNat 64 expected
  | _ => false

def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

/-- A `Raise`/`Return` rejection from the oracle fixture state: the result is an
explicit control `Error` at the original clock, with the original local `x`,
sampled empty global and memory lookups, and the untouched test FFI state
(empty event list). -/
def errorPreservesKeptAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error locals globals memory ffi), n), _) =>
      n == clock && isWordOption 3 (locals "x") &&
        (globals "g").isNone && (globals "x").isNone &&
        (memory 0).isNone && (memory 8).isNone &&
        ffi.state == () && decide (ffi.ioEvents = ([] : List FfiEvent))
  | _ => false

/-- A successful `Return`: cleared locals and the exact HOL payload
`[ValWord 7w]`. -/
def isReturnedCleared (clock expected : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.returned locals _ _ _ values), n), _) =>
      n == clock && isMissingLocal (locals "x") && isWordList expected values
  | _ => false

/-- A successful `Raise`: cleared locals, the exact HOL exception identifier and
payload `Exception E (ValWord 7w)`. -/
def isRaisedCleared (clock : Nat) (exceptionId : String) (expected : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.raised locals _ _ _ exception value), n), _) =>
      n == clock && isMissingLocal (locals "x") && exception == exceptionId &&
        isWordValue expected value
  | _ => false

def retEvalFail : Prog Word64 := .return (.var .local "z")

def retOversized : Prog Word64 := .return (.rStruct (List.replicate 33 (.const 0)))

def retOk : Prog Word64 := .return (.const (BitVec.ofNat 64 7))

def raiseMissingShape : Prog Word64 := .raise "E" (.const (BitVec.ofNat 64 7))

def raiseMismatch : Prog Word64 := .raise "E" (.rStruct [.const (BitVec.ofNat 64 7)])

def raiseEvalFail : Prog Word64 := .raise "E" (.var .local "z")

def raiseOversized : Prog Word64 :=
  .raise "E" (.rStruct (List.replicate 33 (.const 0)))

def oneExceptionContracts : Option PanValueCallContracts :=
  some (contractsWith [("E", .one)])

def oversizedExceptionContracts : Option PanValueCallContracts :=
  some (contractsWith [("E", .comb (List.replicate 33 .one))])

def retEvalFailGuard : Bool := errorPreservesKeptAt 5 (returnRaiseEvaluate 5 retEvalFail)

def retOversizedGuard : Bool := errorPreservesKeptAt 5 (returnRaiseEvaluate 5 retOversized)

def retOkGuard : Bool := isReturnedCleared 5 7 (returnRaiseEvaluate 5 retOk)

def raiseMissingShapeGuard : Bool :=
  errorPreservesKeptAt 5 (returnRaiseEvaluate 5 raiseMissingShape (some (contractsWith [])))

def raiseMismatchGuard : Bool :=
  errorPreservesKeptAt 5 (returnRaiseEvaluate 5 raiseMismatch oneExceptionContracts)

def raiseEvalFailGuard : Bool :=
  errorPreservesKeptAt 5 (returnRaiseEvaluate 5 raiseEvalFail oneExceptionContracts)

def raiseOversizedGuard : Bool :=
  errorPreservesKeptAt 5 (returnRaiseEvaluate 5 raiseOversized oversizedExceptionContracts)

def raiseOkGuard : Bool :=
  isRaisedCleared 5 "E" 7
    (returnRaiseEvaluate 5 (.raise "E" (.const (BitVec.ofNat 64 7))) oneExceptionContracts)

def returnRaiseGuard : Bool :=
  retEvalFailGuard && retOversizedGuard && retOkGuard && raiseMissingShapeGuard &&
    raiseMismatchGuard && raiseEvalFailGuard && raiseOversizedGuard && raiseOkGuard

#guard returnRaiseGuard

def runChecks : IO Bool := do
  if retEvalFailGuard then
    IO.println "PASS panSem Return failing expression rejected with Error and unchanged state"
  else IO.println "FAIL panSem Return failing expression rejected with Error and unchanged state"
  if retOversizedGuard then
    IO.println "PASS panSem Return oversized payload rejected with Error and unchanged state"
  else IO.println "FAIL panSem Return oversized payload rejected with Error and unchanged state"
  if retOkGuard then
    IO.println "PASS panSem Return well-sized payload is ValWord 7w and clears locals"
  else IO.println "FAIL panSem Return well-sized payload is ValWord 7w and clears locals"
  if raiseMissingShapeGuard then
    IO.println "PASS panSem Raise missing exception shape rejected with Error and unchanged state"
  else IO.println "FAIL panSem Raise missing exception shape rejected with Error and unchanged state"
  if raiseMismatchGuard then
    IO.println "PASS panSem Raise mismatched exception shape rejected with Error and unchanged state"
  else IO.println "FAIL panSem Raise mismatched exception shape rejected with Error and unchanged state"
  if raiseEvalFailGuard then
    IO.println "PASS panSem Raise failing expression rejected with Error and unchanged state"
  else IO.println "FAIL panSem Raise failing expression rejected with Error and unchanged state"
  if raiseOversizedGuard then
    IO.println "PASS panSem Raise oversized payload rejected with Error and unchanged state"
  else IO.println "FAIL panSem Raise oversized payload rejected with Error and unchanged state"
  if raiseOkGuard then
    IO.println "PASS panSem Raise well-matched exception E payload ValWord 7w clears locals"
  else IO.println "FAIL panSem Raise well-matched exception E payload ValWord 7w clears locals"
  pure returnRaiseGuard

end Flapjack.Test.PanSemReturnRaiseErrorParity
