import Flapjack.Pancake.Semantics.PanSem
import Flapjack.PanValueFfiClockSemantics
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `DecCall` Error result

The source oracle is `scripts/hol-probes/pan_sem_deccall_error_probe.out`,
generated from `panSemScript.sml` (`DecCall`, lines 694-713). It pins:

* a `DecCall` whose callee returns a value of the declared shape runs the
  continuation and restores the declared local;
* a `DecCall` whose callee returns a value of the wrong shape is rejected
  (`SOME Error`);
* a `DecCall` whose callee body is `Skip`, `Break`, or `Continue` is rejected
  with `SOME Error`, matching the call path that treats the callee's `NONE`,
  `Break`, and `Continue` results as errors;
* a `DecCall` naming an unknown function is rejected (`SOME Error`).

The clocked production entry point `panSemEvaluateCodeStateWithPostState` is
exercised for the successful and rejected cases, and the non-clocked
`evalPanValueFfiProgramSteps` step evaluator is exercised directly for the
shape-mismatch, callee-Error, callee-`Skip`/`Break`/`Continue`, and
missing-function cases.
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

/-- The bad function has a parameter `p = 42`. Its nested DecCall also writes
    `p`, then returns `p`; HOL's `res_var` restores the original parameter
    after the continuation's Return clears locals. -/
def nestedBadShapeCode : PanSemCodeMap Word64 :=
  [("bad", ([ ("p", Shape.one) ],
      .decCall "p" Shape.one "id" [] (.return (.var .local "p")), Shape.one)),
    ("id", ([], .return (.const (BitVec.ofNat 64 7)), Shape.one))]

def nestedBadShapeProgram : Prog Word64 :=
  .decCall "answer" (.named "Other") "bad" [.const (BitVec.ofNat 64 42)] .skip

def nestedBadShapeLocals : VarName → Option (PanValue Word64) :=
  updatePanValueMap (fun _ => none) "p" (.word (BitVec.ofNat 64 42))

theorem nestedBadShapeBindParameters :
    bindPanValueParameters ["p"] [.word (BitVec.ofNat 64 42)] =
      some nestedBadShapeLocals := by
  simp [bindPanValueParameters, nestedBadShapeLocals]

theorem emptyPanValueBindParameters :
    bindPanValueParameters (α := Word64) ([] : List VarName)
      ([] : List (PanValue Word64)) = some (fun _ => none) := by
  rfl

def isWord (value : BitVec 64) : Option (PanValue Word64) → Bool
  | some (.word w) => w == value
  | _ => false

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

def nestedBadShapeExpectedState : PanSemState Word64 (FfiState Unit) :=
  { decCallState 10 nestedBadShapeCode with
    locals := nestedBadShapeLocals
    clock := 8 }

def nestedBadShapeResult := decCallEvaluate 10 nestedBadShapeCode nestedBadShapeProgram

/- Exact equality of the complete source post-state. This checks the whole
    local function, globals, memory, FFI, clock, code, structs, domains, and
    source addresses carried by `PanSemState`, not selected map lookups. The
    direct HOL probe also EVALs a Boolean comparison of its entire returned
    `SND` against the corresponding `nestedState` update; the oracle row is
    `nested_deccall_bad_shape_state_exact=T`. -/
set_option linter.unusedSimpArgs false in
theorem nestedBadShapeResultExact : nestedBadShapeResult = some
    ((.control (.error nestedBadShapeLocals (fun _ => none) (fun _ => none)
        statefulTestFfiState), 8), nestedBadShapeExpectedState) := by
  simp (config := { decide := true }) [nestedBadShapeResult, decCallEvaluate,
    panSemEvaluateCodeStateWithPostState,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemProgFuel, panSemExpFuel, panSemExpListFuel, panSemCodeBodyFuel,
    panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockCodeDecCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiClockProg, evalPanValueFfiClockCall,
    evalPanValueFfiProgSteps, evalPanValueFfiCallSteps,
    evalPanValueExpCounted, evalPanValueExpsCounted, panValueReturnResult,
    panValuePayloadWithinLimit, panValueExpStepCost, updatePanValueMap,
    restorePanValueLocal, restorePanValueFfiLocal, panValueFfiClockRestoreLocal,
    fixPanClock, decPanClock,
    lookupPanSemCodeCall,
    panSemCodeLookup, lookupInfo, panSemCodeArgumentsMatch, bindPanValueParameters,
    panValueCallArgumentsValue, panValueCallArguments, panValueCallTarget,
    panValueParametersValid, nestedBadShapeBindParameters, bindPanValueParameters,
    lookupPanFunction, panValueReturnValid,
    panValueShape, panShapeMatches, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    evalPanValueExp,
    nestedBadShapeExpectedState, nestedBadShapeLocals, nestedBadShapeProgram,
    nestedBadShapeCode, decCallState]
  all_goals
    funext key
    simp [restorePanValueLocal, updatePanValueMap, nestedBadShapeLocals, beq_iff_eq]

def nestedBadShapeClockedListResult :
    Option (PanValueFfiClockResult Word64 Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [("bad", ["p"], (.decCall "p" .one "id" [] (.return (.var .local "p")) : Prog Word64)),
        ("id", [], (.return (.const (BitVec.ofNat 64 7)) : Prog Word64))]
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 10
    nestedBadShapeProgram

/- Exact outcome for the clocked list-function evaluator, including its
    complete returned locals function. -/
set_option linter.unusedSimpArgs false in
theorem nestedBadShapeClockedListExact : nestedBadShapeClockedListResult = some
    (.control (.error nestedBadShapeLocals (fun _ => none) (fun _ => none)
      statefulTestFfiState), 8) := by
  simp (config := { decide := true }) [nestedBadShapeClockedListResult,
    evalPanValueFfiClockProg, evalPanValueFfiClockCall, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps, evalPanValueFfiCallSteps, evalPanValueExpCounted,
    evalPanValueExpsCounted, panValueReturnResult, panValuePayloadWithinLimit,
    panValueExpStepCost, updatePanValueMap, restorePanValueLocal,
    restorePanValueFfiLocal, panValueFfiClockRestoreLocal, fixPanClock, decPanClock,
    panValueCallArgumentsValue, panValueCallArguments, panValueCallTarget,
    panValueParametersValid, nestedBadShapeBindParameters, emptyPanValueBindParameters,
    lookupPanFunction, panValueReturnValid,
    panValueShape, panShapeMatches, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    evalPanValueExp, nestedBadShapeLocals, nestedBadShapeProgram]
  all_goals first
    | simpa [panValueExpStepCost.panValueExpsStepCost, panValueExpStepCost]
    | (funext key; simp [nestedBadShapeLocals, restorePanValueLocal,
        updatePanValueMap, beq_iff_eq])

def nestedBadShapeClockedListGuard : Bool :=
  match nestedBadShapeClockedListResult with
  | some (.control (.error locals _ _ _), clock) =>
      clock == 8 && isWord 42 (locals "p")
  | _ => false

def nestedBadShapeNonClockedFunctions : List (FunName × List VarName × Prog Word64) :=
  [("bad", ["p"], .decCall "p" .one "id" [] (.return (.var .local "p"))),
    ("id", [], .return (.const (BitVec.ofNat 64 7)))]

def nestedBadShapeNonClockedResult : Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] nestedBadShapeNonClockedFunctions (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState nestedBadShapeProgram

/- Exact result and step count for the nonclocked step evaluator. -/
set_option linter.unusedSimpArgs false in
theorem nestedBadShapeNonClockedExact : nestedBadShapeNonClockedResult = some
    (.error nestedBadShapeLocals (fun _ => none) (fun _ => none)
      statefulTestFfiState, 7) := by
  simp (config := { decide := true }) [nestedBadShapeNonClockedResult,
    evalPanValueFfiProgramSteps, evalPanValueFfiProgSteps,
    evalPanValueFfiCallSteps, evalPanValueExpCounted, evalPanValueExpsCounted,
    panValueReturnResult, panValuePayloadWithinLimit, panValueExpStepCost,
    panValueExpsStepCost,
    updatePanValueMap, restorePanValueLocal, restorePanValueFfiLocal,
    panValueCallArguments, panValueCallTarget, panValueReturnValid, panValueShape,
    nestedBadShapeBindParameters, emptyPanValueBindParameters,
    bindPanValueParameters, lookupPanFunction,
    panShapeMatches, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    evalPanValueExp, nestedBadShapeNonClockedFunctions, nestedBadShapeProgram,
    nestedBadShapeLocals]
  all_goals first
    | simp [panValueExpStepCost.panValueExpsStepCost, panValueExpStepCost]
    | (funext key; simp [nestedBadShapeLocals, restorePanValueLocal,
        updatePanValueMap, beq_iff_eq])

def nestedBadShapeNonClockedGuard : Bool :=
  match nestedBadShapeNonClockedResult with
  | some (.error locals _ _ _, _) => isWord 42 (locals "p")
  | _ => false


def deccallOkProgram : Prog Word64 :=
  .decCall "r" Shape.one "f" [] .skip

def deccallShapeProgram : Prog Word64 :=
  .decCall "r" (Shape.named "Other") "f" [] .skip

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
def deccallNestedBadShapeGuard : Bool := nestedBadShapeClockedListGuard && nestedBadShapeNonClockedGuard

def calleeSkipCode : PanSemCodeMap Word64 := [("s", ([], .skip, Shape.one))]
def calleeBreakCode : PanSemCodeMap Word64 := [("b", ([], .break, Shape.one))]
def calleeContinueCode : PanSemCodeMap Word64 := [("c", ([], .continue, Shape.one))]

def deccallNamedProgram (name : FunName) : Prog Word64 :=
  .decCall "r" Shape.one name [] .skip

/-- The Call/DecCall path rejects a successful callee (HOL `NONE`), a `Break`
    or `Continue` callee, and a missing function lookup, each as `SOME Error`. -/
def deccallMissingGuard : Bool := isErrorResult (decCallEvaluate 5 calleeCode (deccallNamedProgram "missing"))
def deccallSkipGuard : Bool := isErrorResult (decCallEvaluate 5 calleeSkipCode (deccallNamedProgram "s"))
def deccallBreakGuard : Bool := isErrorResult (decCallEvaluate 5 calleeBreakCode (deccallNamedProgram "b"))
def deccallContinueGuard : Bool := isErrorResult (decCallEvaluate 5 calleeContinueCode (deccallNamedProgram "c"))

def nonClockedFunctionsNamed (name : FunName) (code : Prog Word64) :
    List (FunName × List VarName × Prog Word64) :=
  [(name, [], code)]

def nonClockedEvaluateNamed (name : FunName) (code : Prog Word64) (program : Prog Word64) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] (nonClockedFunctionsNamed name code) (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 3 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState program

def nonClockedIsErrorNamed (name : FunName) (code : Prog Word64)
    (program : Prog Word64) : Bool :=
  match nonClockedEvaluateNamed name code program with
  | some (.error _ _ _ _, _) => true
  | _ => false

def deccallNcMissingGuard : Bool :=
  nonClockedIsErrorNamed "missing" .skip (deccallNamedProgram "missing")
def deccallNcSkipGuard : Bool :=
  nonClockedIsErrorNamed "s" .skip (deccallNamedProgram "s")
def deccallNcBreakGuard : Bool :=
  nonClockedIsErrorNamed "b" .break (deccallNamedProgram "b")
def deccallNcContinueGuard : Bool :=
  nonClockedIsErrorNamed "c" .continue (deccallNamedProgram "c")

/-- A `DecCall` whose argument list fails to evaluate (an unbound local),
    which HOL rejects before callee lookup. -/
def deccallArgFailProgram (name : FunName) : Prog Word64 :=
  .decCall "r" Shape.one name [.var .local "z"] .skip

/-- True when evaluation yields an explicit `Error` at the given clock with the
    pre-existing local `x` still bound to `3`. -/
def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error locals _ _ _), n), _) => n == clock && isWord 3 (locals "x")
  | _ => false

def deccallArgFailGuard : Bool :=
  isErrorAt 5 (decCallEvaluate 5 calleeCode (deccallArgFailProgram "f"))
def deccallArgFailMissingGuard : Bool :=
  isErrorAt 5 (decCallEvaluate 5 calleeCode (deccallArgFailProgram "missing"))
def deccallNcArgFailGuard : Bool :=
  nonClockedIsErrorNamed "f" calleeBody (deccallArgFailProgram "f")
def deccallNcArgFailMissingGuard : Bool :=
  nonClockedIsErrorNamed "missing" .skip (deccallArgFailProgram "missing")

#guard deccallOkGuard
#guard deccallShapeGuard
#guard deccallCalleeErrorGuard
#guard deccallNonClockedShapeGuard
#guard deccallNonClockedErrorGuard
#guard deccallNestedBadShapeGuard
#guard deccallMissingGuard
#guard deccallSkipGuard
#guard deccallBreakGuard
#guard deccallContinueGuard
#guard deccallNcMissingGuard
#guard deccallNcSkipGuard
#guard deccallNcBreakGuard
#guard deccallNcContinueGuard
#guard deccallArgFailGuard
#guard deccallArgFailMissingGuard
#guard deccallNcArgFailGuard
#guard deccallNcArgFailMissingGuard

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
  let nested := deccallNestedBadShapeGuard
  IO.println (if nested then "PASS nested DecCall mismatch preserves parameter across all evaluator paths"
    else "FAIL nested DecCall mismatch preserves parameter across all evaluator paths")
  let missing := deccallMissingGuard && deccallNcMissingGuard
  IO.println (if missing then "PASS panSem Call missing function rejected with Error"
    else "FAIL panSem Call missing function rejected with Error")
  let skip := deccallSkipGuard && deccallNcSkipGuard
  IO.println (if skip then "PASS panSem Call falling-through callee rejected with Error"
    else "FAIL panSem Call falling-through callee rejected with Error")
  let brk := deccallBreakGuard && deccallNcBreakGuard
  IO.println (if brk then "PASS panSem Call Break callee rejected with Error"
    else "FAIL panSem Call Break callee rejected with Error")
  let cont := deccallContinueGuard && deccallNcContinueGuard
  IO.println (if cont then "PASS panSem Call Continue callee rejected with Error"
    else "FAIL panSem Call Continue callee rejected with Error")
  let argFail := deccallArgFailGuard && deccallArgFailMissingGuard &&
    deccallNcArgFailGuard && deccallNcArgFailMissingGuard
  IO.println (if argFail then "PASS panSem Call failing argument rejected with Error before lookup"
    else "FAIL panSem Call failing argument rejected with Error before lookup")
  pure (ok && shape && callee && ncShape && ncErr && nested && missing && skip && brk && cont && argFail)

end Flapjack.Test.PanSemDecCallErrorParity
