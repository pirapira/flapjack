import Flapjack.PanToCrepCorrectnessBridge

namespace Flapjack

/-! A concrete, executable instantiation of the `pc_compile_correct` boundary
    for the source `Skip` constructor.  The evaluator adapters are the same
    compact evaluators used by the general bridge; code and exception shape
    relations are deliberately trivial here so the theorem isolates the
    evaluator/state simulation rather than hiding it behind a hypothesis. -/

def skipNatPrimitive : PanPrimitiveHandler Nat :=
  fun _ _ => none

def skipNatSourceHandler : PanValueFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

def skipNatCrepPrimitive : CrepPrimitiveHandler Nat :=
  fun _ _ => none

def skipNatFfi : CrepFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

def skipNatSharedMem : CrepSharedMemHandler Nat :=
  fun _ _ _ _ => none

def skipNatCodeRel : PanValuePcCodeRel Nat :=
  fun _ _ _ => True

def skipNatExcpRel : PanValuePcExceptionShapeRel Nat :=
  fun _ _ _ => True

def skipNatExceptionCode : ExceptionId → Option Nat :=
  fun _ => none

def skipNatGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat) :=
  fun _ _ => none

theorem panValuePcCompileCorrect_compact_skip_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.skip : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_tick_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.tick : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_break_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.break : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_continue_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.continue : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_annot_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.annot "tag" "text" : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_return_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 1)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 1)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.return (.const 7) : Prog Nat) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hlimit : panValuePayloadWithinLimit structs (.word (7 : Nat)) = true :=
    panValuePayloadWithinLimit_word structs 7
  have hsourceResult :
      ({ code := sourceInput.code
        , eshapes := sourceInput.eshapes
        , result := panValuePcResultOfControl
            (.returned (fun _ => none) sourceInput.globals sourceInput.memory
              [.word 7]) } : PanValuePcExecution Nat) = sourceExecution := by
    simpa [panValuePcCompactSourceEvaluator,
      evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp, hlimit] using hsource
  cases hsourceResult
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpsState, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  have hstateRel :
      panValueCrepStateRel structs context
        (fun _ => none) sourceInput.globals sourceInput.memory targetInput.state :=
    ⟨hstate.1, panValueCrepLocalsRel_empty structs context targetInput.state.locals,
      hstate.2.2⟩
  exact ⟨hstateRel, panValueCrepValuesRel_singleton (.word 7)⟩

theorem panValuePcCompileCorrect_compact_seq_skip_tick_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup (.seq (.skip : Prog Nat) .tick) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_if_zero_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.ite (.const 0) (.skip : Prog Nat) .tick) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_while_zero_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.while (.const 0) (.skip : Prog Nat)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_dec_skip_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.dec "x" .one (.const 7) (.skip : Prog Nat)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
    panValueShape, panShapeMatches, restorePanValueControlLocal] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState, restoreCrepResult, allocatedNames,
    nestedDecs]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  have hsourceLocals :
      restorePanValueLocal
          (updatePanValueMap sourceInput.locals "x" (.word (7 : Nat))) "x"
          (sourceInput.locals "x") = sourceInput.locals := by
    funext current
    by_cases hcurrent : current = "x" <;>
      simp [restorePanValueLocal, updatePanValueMap, hcurrent]
  have htargetLocals :
      restoreCrepLocal
          (updateCrepLocal targetInput.state.locals (context.maxVar + 1) 7)
          (context.maxVar + 1) (targetInput.state.locals (context.maxVar + 1)) =
        targetInput.state.locals := by
    funext current
    by_cases hcurrent : current = context.maxVar + 1 <;>
      simp [restoreCrepLocal, updateCrepLocal, hcurrent]
  rw [hsourceLocals, htargetLocals]
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_dec_assign_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 3)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 3)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.dec "x" .one (.const 7)
        (.assign .local "x" (.const 8))) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
    panValueShape, panShapeMatches, restorePanValueControlLocal,
    panValueAssignmentValid, updatePanValueMap] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState, restoreCrepResult, allocatedNames,
    nestedDecs, crepNestedSeq, distinctLists, assignExistingCrepValues, crepNamesDistinct,
    crepLocalsDefined, lookupInfo, updateCrepLocal]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  have hsourceLocals :
      restorePanValueLocal
          (updatePanValueMap
            (updatePanValueMap sourceInput.locals "x" (.word (7 : Nat))) "x"
            (.word (8 : Nat))) "x" (sourceInput.locals "x") =
        sourceInput.locals := by
    funext current
    by_cases hcurrent : current = "x" <;>
      simp [restorePanValueLocal, updatePanValueMap, hcurrent]
  have htargetLocals :
      restoreCrepLocal
          (updateCrepLocal
            (updateCrepLocal targetInput.state.locals (context.maxVar + 1) 7)
            (context.maxVar + 1) 8)
          (context.maxVar + 1) (targetInput.state.locals (context.maxVar + 1)) =
        targetInput.state.locals := by
    funext current
    by_cases hcurrent : current = context.maxVar + 1 <;>
      simp [restoreCrepLocal, updateCrepLocal, hcurrent]
  rw [hsourceLocals, htargetLocals]
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_if_nonzero_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.ite (.const 5) (.skip : Prog Nat) .tick) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_if_nonzero_break_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.ite (.const 5) .break (.skip : Prog Nat)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_if_nonzero_continue_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.ite (.const 5) .continue (.skip : Prog Nat)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  simp [panValuePcCompactSourceEvaluator,
    evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp] at hsource
  cases hsource
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  simpa [panValuePcResultOfControl, panValuePcResultRel,
    panValueCrepControlRel] using hstate

theorem panValuePcCompileCorrect_compact_if_nonzero_return_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 2)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 2)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.ite (.const 5) (.return (.const 7)) (.skip : Prog Nat)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hlimit : panValuePayloadWithinLimit structs (.word (7 : Nat)) = true :=
    panValuePayloadWithinLimit_word structs 7
  have hsourceResult :
      ({ code := sourceInput.code
        , eshapes := sourceInput.eshapes
        , result := panValuePcResultOfControl
            (.returned (fun _ => none) sourceInput.globals sourceInput.memory
              [.word 7]) } : PanValuePcExecution Nat) = sourceExecution := by
    simpa [panValuePcCompactSourceEvaluator,
      evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp, hlimit] using hsource
  cases hsourceResult
  simp [crepPcCompactTargetEvaluator, evalCrepFullProgState, compileProg,
    compileExp, evalCrepFullExpsState, evalCrepFullExpState]
    at htarget
  obtain ⟨targetResult, htargetResult, htargetExecution⟩ := htarget
  cases htargetExecution
  simp [crepPcResultOfControl] at htargetResult
  cases htargetResult
  have hstateRel :
      panValueCrepStateRel structs context
        (fun _ => none) sourceInput.globals sourceInput.memory targetInput.state :=
    ⟨hstate.1, panValueCrepLocalsRel_empty structs context targetInput.state.locals,
      hstate.2.2⟩
  exact ⟨hstateRel, panValueCrepValuesRel_singleton (.word 7)⟩

private theorem skipNatStoreConstSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.store (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) =
    some (.normal locals globals (updatePanValueMemory memory 7 (.word 9))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, panValueStoreWithAccess, panValueFlatStoreWords,
    panValueFlatWords, panValueFlatWordsFuel, panValueFlatOffset,
    updatePanValueMemory]

private theorem skipNatStoreConstTargetEval
    (context : CompileContext Nat) (state : CrepState Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.store (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp)) =
    some (.normal { state with memory := updateMemory state.memory 7 9 }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, nestedDecs, crepNestedSeq,
    stores, freshNames, evalCrepFullProgState, evalCrepFullExpState,
    updateCrepLocal, restoreCrepResult]
  funext current
  by_cases haddress : current = context.maxVar + 1
  · simp [restoreCrepLocal, haddress]
  by_cases hvalue : current = context.maxVar + 2
  · simp [restoreCrepLocal, hvalue]
  · simp [restoreCrepLocal, updateCrepLocal, haddress, hvalue]

theorem panValuePcCompileCorrect_compact_store_const_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.store (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStoreConstSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory
  have htargetEval := skipNatStoreConstTargetEval context targetInput.state
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory 7 9
        hstate.2.2⟩

private theorem skipNatStore32ConstSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.store32 (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) =
    some (.normal locals globals (updatePanValueMemory memory 7 (.word 9))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, updatePanValueMemory]

private theorem skipNatStore32ConstTargetEval
    (context : CompileContext Nat) (state : CrepState Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.store32 (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp)) =
    some (.normal { state with memory := updateMemory state.memory 7 9 }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, evalCrepFullProgState,
    evalCrepFullExpState]

theorem panValuePcCompileCorrect_compact_store32_const_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.store32 (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStore32ConstSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory
  have htargetEval := skipNatStore32ConstTargetEval context targetInput.state
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory 7 9
        hstate.2.2⟩

private theorem skipNatStoreByteConstSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.storeByte (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) =
    some (.normal locals globals (updatePanValueMemory memory 7 (.word 9))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, updatePanValueMemory]

private theorem skipNatStoreByteConstTargetEval
    (context : CompileContext Nat) (state : CrepState Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.storeByte (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp)) =
    some (.normal { state with memory := updateMemory state.memory 7 9 }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, evalCrepFullProgState,
    evalCrepFullExpState]

theorem panValuePcCompileCorrect_compact_storeByte_const_nat :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.storeByte (SourceWordExp.const 7).toExp (SourceWordExp.const 9).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStoreByteConstSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory
  have htargetEval := skipNatStoreByteConstTargetEval context targetInput.state
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory 7 9
        hstate.2.2⟩

end Flapjack
