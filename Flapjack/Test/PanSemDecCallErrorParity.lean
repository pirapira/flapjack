import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `DecCall` Error result

The source oracle is `scripts/hol-probes/pan_sem_deccall_error_probe.out`,
generated from `panSemScript.sml` (`DecCall`, lines 694-713). It pins:

* a `DecCall` whose callee returns a value of the declared shape runs the
  continuation and restores the declared local;
* a `DecCall` whose callee returns a value of the wrong shape is rejected
  (`SOME Error`);
* a `DecCall` whose callee body itself fails is rejected (`SOME Error`);
* a `DecCall` naming an unknown function is rejected (`SOME Error`); this
  remains a tracked gap in the shared call-lookup path and is recorded by the
  oracle but not asserted here.

The clocked production entry point `panSemEvaluateCodeStateWithPostState` is
exercised for the successful and rejected cases, and the non-clocked
`evalPanValueFfiProgramSteps` step evaluator is exercised directly for the
shape-mismatch and callee-Error propagation.
-/

namespace Flapjack.Test.PanSemDecCallErrorParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- The callee returns the constant `7`. -/
def calleeBody : Prog Word64 :=
  .return (.const (BitVec.ofNat 64 7))

/-- The callee assigns an unbound local, so its body is rejected. -/
def calleeErrorBody : Prog Word64 :=
  .assign .local "q" (.const (BitVec.ofNat 64 7))

def calleeCode : PanSemCodeMap Word64 :=
  [("f", ([], calleeBody, Shape.one))]

def calleeErrorCode : PanSemCodeMap Word64 :=
  [("f", ([], calleeErrorBody, Shape.one))]

def decCallState (clock : Nat) (code : PanSemCodeMap Word64) :
    PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
    structs := []
    code := code
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def decCallEvaluate (clock : Nat) (code : PanSemCodeMap Word64)
    (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (decCallState clock code) program

def deccallOkProgram : Prog Word64 :=
  .decCall "r" Shape.one "f" [] .skip

def deccallShapeProgram : Prog Word64 :=
  .decCall "r" (Shape.named "Other") "f" [] .skip

def isWord (value : BitVec 64) : Option (PanValue Word64) → Bool
  | some (.word w) => w == value
  | _ => false

/-- True when evaluation yields exactly an explicit `Error` control result. -/
def isErrorResult
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), _), _) => true
  | _ => false

/-- True when evaluation completes normally at the given clock with the
    pre-existing local `x` still bound to `3`. -/
def isNormalAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.normal locals _ _ _), n), _) => n == clock && isWord 3 (locals "x")
  | _ => false

/-- The non-clocked step evaluator driven with an explicit callee list. -/
def nonClockedFunctions (code : Prog Word64) :
    List (FunName × List VarName × Prog Word64) :=
  [("f", [], code)]

def nonClockedEvaluate (code : Prog Word64) (program : Prog Word64) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] (nonClockedFunctions code) (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 3 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState program

def nonClockedIsError (code : Prog Word64) (program : Prog Word64) : Bool :=
  match nonClockedEvaluate code program with
  | some (.error _ _ _ _, _) => true
  | _ => false

/-- The successful `DecCall` runs the continuation and keeps the pre-existing
    local at the callee's decremented clock. -/
def deccallOkGuard : Bool := isNormalAt 4 (decCallEvaluate 5 calleeCode deccallOkProgram)
def deccallShapeGuard : Bool := isErrorResult (decCallEvaluate 5 calleeCode deccallShapeProgram)
def deccallCalleeErrorGuard : Bool := isErrorResult (decCallEvaluate 5 calleeErrorCode deccallOkProgram)
def deccallNonClockedShapeGuard : Bool := nonClockedIsError calleeBody deccallShapeProgram
def deccallNonClockedErrorGuard : Bool := nonClockedIsError calleeErrorBody deccallOkProgram

#guard deccallOkGuard
#guard deccallShapeGuard
#guard deccallCalleeErrorGuard
#guard deccallNonClockedShapeGuard
#guard deccallNonClockedErrorGuard

def runChecks : IO Bool := do
  let ok := deccallOkGuard
  IO.println (if ok then "PASS panSem DecCall accepted run restores local at callee clock"
    else "FAIL panSem DecCall accepted run restores local at callee clock")
  let shape := deccallShapeGuard
  IO.println (if shape then "PASS panSem DecCall wrong-shape return rejected with Error"
    else "FAIL panSem DecCall wrong-shape return rejected with Error")
  let callee := deccallCalleeErrorGuard
  IO.println (if callee then "PASS panSem DecCall failing callee rejected with Error"
    else "FAIL panSem DecCall failing callee rejected with Error")
  let ncShape := deccallNonClockedShapeGuard
  IO.println (if ncShape then "PASS non-clocked DecCall wrong-shape return rejected with Error"
    else "FAIL non-clocked DecCall wrong-shape return rejected with Error")
  let ncErr := deccallNonClockedErrorGuard
  IO.println (if ncErr then "PASS non-clocked DecCall callee Error propagated"
    else "FAIL non-clocked DecCall callee Error propagated")
  pure (ok && shape && callee && ncShape && ncErr)

end Flapjack.Test.PanSemDecCallErrorParity