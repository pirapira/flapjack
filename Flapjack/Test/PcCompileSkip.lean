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

private theorem skipNatStoreSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (address value : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.store (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) =
    some (.normal locals globals (updatePanValueMemory memory address (.word value))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, panValueStoreWithAccess, panValueFlatStoreWords,
    panValueFlatWords, panValueFlatWordsFuel, panValueFlatOffset,
    updatePanValueMemory]

private theorem skipNatStoreTargetEval
    (context : CompileContext Nat) (state : CrepState Nat) (address value : Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.store (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp)) =
    some (.normal { state with memory := updateMemory state.memory address value }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, nestedDecs, crepNestedSeq,
    stores, freshNames, evalCrepFullProgState, evalCrepFullExpState,
    updateCrepLocal, restoreCrepResult]
  funext current
  by_cases haddress : current = context.maxVar + 1
  · simp [restoreCrepLocal, haddress]
  by_cases hvalue : current = context.maxVar + 2
  · simp [restoreCrepLocal, hvalue]
  · simp [restoreCrepLocal, updateCrepLocal, haddress, hvalue]

theorem panValuePcCompileCorrect_compact_store_nat (address value : Nat) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.store (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStoreSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory address value
  have htargetEval := skipNatStoreTargetEval context targetInput.state address value
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory
        address value hstate.2.2⟩

private theorem skipNatStore32SourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (address value : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.store32 (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) =
    some (.normal locals globals (updatePanValueMemory memory address (.word value))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, updatePanValueMemory]

private theorem skipNatStore32TargetEval
    (context : CompileContext Nat) (state : CrepState Nat) (address value : Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.store32 (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp)) =
    some (.normal { state with memory := updateMemory state.memory address value }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, evalCrepFullProgState,
    evalCrepFullExpState]

theorem panValuePcCompileCorrect_compact_store32_nat (address value : Nat) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.store32 (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStore32SourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory address value
  have htargetEval := skipNatStore32TargetEval context targetInput.state address value
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory
        address value hstate.2.2⟩

private theorem skipNatStoreByteSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (address value : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.storeByte (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) =
    some (.normal locals globals (updatePanValueMemory memory address (.word value))) := by
  simp [SourceWordExp.toExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp, updatePanValueMemory]

private theorem skipNatStoreByteTargetEval
    (context : CompileContext Nat) (state : CrepState Nat) (address value : Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context
        (.storeByte (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp)) =
    some (.normal { state with memory := updateMemory state.memory address value }) := by
  simp [SourceWordExp.toExp, compileProg, compileExp, evalCrepFullProgState,
    evalCrepFullExpState]

theorem panValuePcCompileCorrect_compact_storeByte_nat (address value : Nat) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 4)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.storeByte (SourceWordExp.const address).toExp (SourceWordExp.const value).toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatStoreByteSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory address value
  have htargetEval := skipNatStoreByteTargetEval context targetInput.state address value
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory
        address value hstate.2.2⟩

/-! ### Raise evaluation helpers for the deep store/Raise obligation

    The arbitrary-Raise evidence obligation ultimately needs the source
    `raise` control result and the compiled target `raise` result in an
    explicit, state-visible form.  These two lemmas provide exactly that for
    the constant-payload case used by the compact instances: the source
    evaluator yields `.raised (fun _ => none) globals memory exception (.word
    value)`, and the compiled program (nested payload declarations followed
    by `storeGlobals` into the global spill area and a `.raise code`) yields
    `.raised` of the state whose global area received the payload, with the
    payload temporaries restored.  The exception code comes from the context
    exception map, so the target statement carries that lookup as an explicit
    premise. -/

theorem skipNatRaiseConstSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (exception : ExceptionId) (value : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 4 locals globals memory
      (.raise exception (.const value)) =
    some (.raised (fun _ => none) globals memory exception (.word value)) := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp]

theorem skipNatRaiseConstTargetEval
    (context : CompileContext Nat) (state : CrepState Nat)
    (exception : ExceptionId) (value code : Nat)
    (hcode : lookupInfo exception context.exceptions = some code) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 4 state
      (compileProg context (.raise exception (.const value))) =
    some (.raised { state with
      globals := updateMemory state.globals 0 value } code) := by
  simp [compileProg, compileExp, nestedDecs, crepNestedSeq,
    storeGlobals, freshNames, evalCrepFullProgState, evalCrepFullExpState,
    updateCrepLocal, restoreCrepResult, hcode]
  funext current
  by_cases hcurrent : current = context.maxVar + 1
  · simp [restoreCrepLocal, hcurrent]
  · simp [restoreCrepLocal, updateCrepLocal, hcurrent]

/-- Regression for the raise helpers: a constant-payload raise evaluates on the
    source side to a raised control result and on the compiled side to a raised
    state that only updates the global spill area. -/
example (context : CompileContext Nat) (state : CrepState Nat)
    (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat))
    (exception : ExceptionId) (value code : Nat)
    (hcode : lookupInfo exception context.exceptions = some code) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
        ([] : StructContext) [] 0 0 1 4 locals globals memory
        (.raise exception (.const value)) =
      some (.raised (fun _ => none) globals memory exception (.word value)) ∧
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
        0 0 4 state (compileProg context (.raise exception (.const value))) =
      some (.raised { state with globals := updateMemory state.globals 0 value }
        code) :=
  ⟨skipNatRaiseConstSourceEval [] locals globals memory exception value,
    skipNatRaiseConstTargetEval context state exception value code hcode⟩

/-- Source evaluation of two sequential constant stores: the memory is updated
    twice while locals, globals and the stored payloads stay visible. -/
private theorem skipNatSeqStoreSourceEval
    (structs : StructContext) (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat))
    (firstAddress firstValue secondAddress secondValue : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi skipNatPrimitive skipNatSourceHandler
      structs [] 0 0 1 5 locals globals memory
      (.seq
        (.store (SourceWordExp.const firstAddress).toExp
          (SourceWordExp.const firstValue).toExp)
        (.store (SourceWordExp.const secondAddress).toExp
          (SourceWordExp.const secondValue).toExp)) =
    some (.normal locals globals
      (updatePanValueMemory
        (updatePanValueMemory memory firstAddress (.word firstValue))
        secondAddress (.word secondValue))) := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfi, skipNatStoreSourceEval]

/-- Compiled evaluation of two sequential constant stores: the nested
    declaration and store bodies compose, updating the target memory twice. -/
private theorem skipNatSeqStoreTargetEval
    (context : CompileContext Nat) (state : CrepState Nat)
    (firstAddress firstValue secondAddress secondValue : Nat) :
    evalCrepFullProgState [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem
      0 0 5 state
      (compileProg context
        (.seq
          (.store (SourceWordExp.const firstAddress).toExp
            (SourceWordExp.const firstValue).toExp)
          (.store (SourceWordExp.const secondAddress).toExp
            (SourceWordExp.const secondValue).toExp))) =
    some (.normal { state with
      memory := updateMemory (updateMemory state.memory firstAddress firstValue)
        secondAddress secondValue }) := by
  rw [compileProg_seq]
  simp [evalCrepFullProgState, skipNatStoreTargetEval]

/-- Concrete correctness for two sequential constant stores: this exercises the
    composition of the store instances and keeps the doubly-updated memory
    relation explicit. -/
theorem panValuePcCompileCorrect_compact_seq_store_nat
    (firstAddress firstValue secondAddress secondValue : Nat) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        skipNatPrimitive skipNatSourceHandler [] 0 0 1 5)
      (crepPcCompactTargetEvaluator
        [] skipNatCrepPrimitive skipNatFfi skipNatSharedMem 0 0 5)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode
      skipNatGlobalsLookup
      (.seq
        (.store (SourceWordExp.const firstAddress).toExp
          (SourceWordExp.const firstValue).toExp)
        (.store (SourceWordExp.const secondAddress).toExp
          (SourceWordExp.const secondValue).toExp)) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  have hsourceEval := skipNatSeqStoreSourceEval sourceInput.structs
    sourceInput.locals sourceInput.globals sourceInput.memory
    firstAddress firstValue secondAddress secondValue
  have htargetEval := skipNatSeqStoreTargetEval context targetInput.state
    firstAddress firstValue secondAddress secondValue
  simp only [panValuePcCompactSourceEvaluator, hsourceEval] at hsource
  simp only [crepPcCompactTargetEvaluator, htargetEval] at htarget
  cases hsource
  cases htarget
  simp only [panValuePcResultOfControl, panValuePcResultRel]
  exact ⟨hstate.1, hstate.2.1, by
    simpa [updateMemory] using
      panValueCrepMemoryRel_update_word
        (updatePanValueMemory sourceInput.memory firstAddress (.word firstValue))
        (updateMemory targetInput.state.memory firstAddress firstValue)
        secondAddress secondValue
        (panValueCrepMemoryRel_update_word sourceInput.memory targetInput.state.memory
          firstAddress firstValue hstate.2.2)⟩

/-- Flat-global evaluator evidence for a constant-word raise payload.

    This builds the giant evaluator-evidence bundle that
    `panValuePcRaisedHraiseData_of_flat_global_evaluator_evidence` consumes,
    specialized to a `(.word value)` payload: the witness expression is
    `.const value`, its flat words are `[value]`, and the raised target state
    is the one-word spill of `value` into the globals. The source/target raise
    equations `skipNatRaiseConstSourceEval`/`skipNatRaiseConstTargetEval`
    identify exactly this globals update, so the explicit `exceptionRel`,
    `lookupInfo` and `exceptionCode` premises connect the equations to the
    generic evidence. All of locals, globals, memory and the exception code
    stay visible. -/
theorem skipNatRaiseConstFlatGlobalEvaluatorEvidence
    (context : CompileContext Nat) (structs : StructContext)
    (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
    (sourceMemory : Nat → Option (PanValue Nat))
    (state : CrepState Nat) (sourceException : ExceptionId) (value : Nat)
    (targetException bytesInWord baseAddress topAddress : Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hfresh : ∀ name ∈ freshNames context 1 1, state.locals name = none)
    (hexception : exceptionRel sourceException (.word value) targetException)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException)
    (hcode : exceptionCode sourceException = some targetException) :
    ∃ (state' : CrepState Nat) (expression : Exp Nat)
      (compiled : List (CrepExp Nat)) (shape : Shape) (values : List Nat),
      { state with globals := updateMemory state.globals 0 value } =
          { state' with globals :=
              updateMemoryListAt state'.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state' ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression = some (.word value) ∧
        panValuePayloadWithinLimit structs (.word value) = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state' baseAddress topAddress compiled =
          some values ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ item ∈ compiled, name ∉ crepExpVars item) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state'.locals name = none) ∧
        exceptionRel sourceException (.word value) targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords (.word value) = values ∧
        List.Pairwise (fun left right : Nat => left ≠ right)
          (storeAddresses (0 : Nat) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs (.word value)) ≤ 32 := by
  refine ⟨state, .const value, [.const value], .one, [value], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [updateMemoryListAt]
  · exact hbytesInWord
  · exact hrel
  · simp [evalPanValueExp]
  · exact panValuePayloadWithinLimit_word structs value
  · simp [compileExp]
  · simp
  · simp [evalCrepFullExpsState, evalCrepFullExpState]
  · intro name _ item hitem
    obtain rfl := List.mem_singleton.mp hitem
    simp
  · simpa using hfresh
  · exact hexception
  · exact hlookupCode
  · exact hcode
  · simp [panValueFlatWords, panValueFlatWordsFuel]
  · simp [storeAddresses]
  · simp [panValueShape]

/-- Symbolic source-word store: the direct compact instance, lifting the full
evaluator relation `compile_full_pan_value_store_source_word_state_relation` to
the compact evaluators.  The address and value are arbitrary `SourceWordExp`s;
the caller supplies the evaluated words together with the compiled-expression
stability facts, so source locals/globals/memory and the target state stay
visible. -/
theorem panValuePcCompileCorrect_compact_store_source_word
    (address value : SourceWordExp Nat)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat)) (name : VarName)
      (currentValue : PanValue Nat), sourceLocals name = some currentValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstoreEvidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (state : CrepState Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory state →
      ∃ addressValue valueValue : Nat,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          address.toExp = some (.word addressValue) ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          value.toExp = some (.word valueValue) ∧
        (∀ compiled, compileExp context address.toExp = ([compiled], .one) →
          evalCrepFullExpState
            ({ state with locals :=
                updateCrepLocal state.locals (context.maxVar + 1) addressValue })
            0 0 compiled = some addressValue) ∧
        (∀ compiled, compileExp context value.toExp = ([compiled], .one) →
          evalCrepFullExpState
            ({ state with locals :=
                updateCrepLocal state.locals (context.maxVar + 1) addressValue })
            0 0 compiled = some valueValue)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator skipNatPrimitive skipNatSourceHandler
        [] 0 0 1 4)
      (crepPcCompactTargetEvaluator [] skipNatCrepPrimitive skipNatFfi
        skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode skipNatGlobalsLookup
      (.store address.toExp value.toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  obtain ⟨addressValue, valueValue, hsourceAddress, hsourceValue, haddressStable,
    hvalueStable⟩ :=
    hstoreEvidence context structs sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state hstate
  have hrelation :=
    compile_full_pan_value_store_source_word_state_relation context structs [] []
      sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
      skipNatPrimitive skipNatSourceHandler skipNatCrepPrimitive skipNatFfi
      skipNatSharedMem 0 0 1 address value addressValue valueValue
      (hbytesInWord context 1) hstate (hlookup context sourceInput.locals)
      hsourceAddress hsourceValue haddressStable hvalueStable
  obtain ⟨hsourceResult, htargetResult, hrelNew⟩ := hrelation
  simp only [panValuePcCompactSourceEvaluator, hsourceStructs, hsourceResult]
    at hsource
  simp only [crepPcCompactTargetEvaluator, htargetResult] at htarget
  cases hsource
  cases htarget
  simpa [panValuePcResultOfControl, panValuePcResultRel] using hrelNew

/-- The symbolic store instance is usable with a non-constant, state-independent
address expression: here the address is `.baseAddr` (evaluating to the base
address `0`) and the value is the constant `9`.  The compiled-expression
stability facts hold because neither compiled expression reads locals. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat)) (name : VarName)
      (currentValue : PanValue Nat), sourceLocals name = some currentValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator skipNatPrimitive skipNatSourceHandler
        [] 0 0 1 4)
      (crepPcCompactTargetEvaluator [] skipNatCrepPrimitive skipNatFfi
        skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode skipNatGlobalsLookup
      (.store (SourceWordExp.baseAddr).toExp (SourceWordExp.const 9).toExp) :=
  panValuePcCompileCorrect_compact_store_source_word
    SourceWordExp.baseAddr (SourceWordExp.const 9) hbytesInWord hlookup
    (by
      intro context structs sourceLocals sourceGlobals sourceMemory state _hstate
      refine ⟨0, 9, ?_, ?_, ?_, ?_⟩
      · simp [SourceWordExp.toExp, evalPanValueExp]
      · simp [SourceWordExp.toExp, evalPanValueExp]
      · intro compiled hcompile
        simp [SourceWordExp.toExp, compileExp] at hcompile
        rw [← hcompile]
        simp [evalCrepFullExpState]
      · intro compiled hcompile
        simp [SourceWordExp.toExp, compileExp] at hcompile
        rw [← hcompile]
        simp [evalCrepFullExpState])

/-- Symbolic source-word store32: the direct compact instance, lifting the full
evaluator relation `compile_full_pan_value_store32_source_word_state_relation`
to the compact evaluators.  The caller supplies the evaluated address/value
words; source locals/globals/memory and the target state stay visible. -/
theorem panValuePcCompileCorrect_compact_store32_source_word
    (address value : SourceWordExp Nat)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat)) (name : VarName)
      (currentValue : PanValue Nat), sourceLocals name = some currentValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstoreEvidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (state : CrepState Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory state →
      ∃ addressValue valueValue : Nat,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          address.toExp = some (.word addressValue) ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          value.toExp = some (.word valueValue)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator skipNatPrimitive skipNatSourceHandler
        [] 0 0 1 4)
      (crepPcCompactTargetEvaluator [] skipNatCrepPrimitive skipNatFfi
        skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode skipNatGlobalsLookup
      (.store32 address.toExp value.toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  obtain ⟨addressValue, valueValue, hsourceAddress, hsourceValue⟩ :=
    hstoreEvidence context structs sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state hstate
  have hrelation :=
    compile_full_pan_value_store32_source_word_state_relation context structs [] []
      sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
      skipNatPrimitive skipNatSourceHandler skipNatCrepPrimitive skipNatFfi
      skipNatSharedMem 0 0 1 3 address value addressValue valueValue
      (hbytesInWord context 1) hstate (hlookup context sourceInput.locals)
      hsourceAddress hsourceValue
  obtain ⟨hsourceResult, compiledAddress, compiledValue, _hcompileAddress,
    _hcompileValue, htargetResult, hrelNew⟩ := hrelation
  simp only [panValuePcCompactSourceEvaluator, hsourceStructs, hsourceResult]
    at hsource
  simp only [crepPcCompactTargetEvaluator, htargetResult] at htarget
  cases hsource
  cases htarget
  simpa [panValuePcResultOfControl, panValuePcResultRel] using hrelNew

/-- Symbolic source-word storeByte: the direct compact instance, lifting the full
evaluator relation `compile_full_pan_value_storeByte_source_word_state_relation`
to the compact evaluators.  The caller supplies the evaluated address/value
words; source locals/globals/memory and the target state stay visible. -/
theorem panValuePcCompileCorrect_compact_storeByte_source_word
    (address value : SourceWordExp Nat)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat)) (name : VarName)
      (currentValue : PanValue Nat), sourceLocals name = some currentValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstoreEvidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (state : CrepState Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory state →
      ∃ addressValue valueValue : Nat,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          address.toExp = some (.word addressValue) ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory 0 0 1
          value.toExp = some (.word valueValue)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator skipNatPrimitive skipNatSourceHandler
        [] 0 0 1 4)
      (crepPcCompactTargetEvaluator [] skipNatCrepPrimitive skipNatFfi
        skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode skipNatGlobalsLookup
      (.storeByte address.toExp value.toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  obtain ⟨addressValue, valueValue, hsourceAddress, hsourceValue⟩ :=
    hstoreEvidence context structs sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state hstate
  have hrelation :=
    compile_full_pan_value_storeByte_source_word_state_relation context structs [] []
      sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
      skipNatPrimitive skipNatSourceHandler skipNatCrepPrimitive skipNatFfi
      skipNatSharedMem 0 0 1 3 address value addressValue valueValue
      (hbytesInWord context 1) hstate (hlookup context sourceInput.locals)
      hsourceAddress hsourceValue
  obtain ⟨hsourceResult, compiledAddress, compiledValue, _hcompileAddress,
    _hcompileValue, htargetResult, hrelNew⟩ := hrelation
  simp only [panValuePcCompactSourceEvaluator, hsourceStructs, hsourceResult]
    at hsource
  simp only [crepPcCompactTargetEvaluator, htargetResult] at htarget
  cases hsource
  cases htarget
  simpa [panValuePcResultOfControl, panValuePcResultRel] using hrelNew

/-- The flat-global raised-data evaluator evidence required by the deep raise
wrapper, specialized to the compact Nat setting used by these regressions. -/
abbrev FlatGlobalRaisedEvidence (bytesInWord baseAddress topAddress : Nat)
    (exceptionCode : ExceptionId → Option Nat) : Prop :=
  ∀ (context : CompileContext Nat) (structs : StructContext)
    (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
    (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
    (sourceValue : PanValue Nat) (targetState : CrepState Nat)
    (targetException : Nat),
    panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) →
    ∃ (state : CrepState Nat) (expression : Exp Nat)
      (compiled : List (CrepExp Nat)) (shape : Shape),
      targetState =
        { state with globals := updateMemoryListAt state.globals 0 context.bytesInWord (panValueFlatWords sourceValue) } ∧
      context.bytesInWord = bytesInWord ∧
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state ∧
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue ∧
      panValuePayloadWithinLimit structs sourceValue = true ∧
      compileExp context expression = (compiled, shape) ∧
      compiled.length = Shape.shapeSize shape ∧
      evalCrepFullExpsState state baseAddress topAddress compiled =
        some (panValueFlatWords sourceValue) ∧
      (∀ name ∈ freshNames context compiled.length 1,
        ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
      (∀ name ∈ freshNames context compiled.length 1,
        state.locals name = none) ∧
      exceptionRel sourceException sourceValue targetException ∧
      lookupInfo sourceException context.exceptions = some targetException ∧
      exceptionCode sourceException = some targetException ∧
      List.Pairwise (fun left right : Nat => left ≠ right)
        (storeAddresses (0 : Nat) context.bytesInWord
          (panValueFlatWords sourceValue).length) ∧
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32

/-- The deep raise wrapper is applicable to an arbitrary source-word payload: it
needs the paired source-word raise bridge premises plus the explicit flat-global
raised-data evaluator evidence, with source locals/globals/memory and the target
state still visible. This example instantiates it on a constant word payload. -/
example
    (hevidence : FlatGlobalRaisedEvidence 1 0 0 skipNatExceptionCode)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookupSource : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (value exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" (.word value) exceptionCode)
    (hlookup : ∀ (targetState : CrepState Nat) (sourceValue : PanValue Nat),
      crepPcFlatGlobalsLookup 1 targetState sourceValue =
        skipNatGlobalsLookup targetState sourceValue) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator skipNatPrimitive skipNatSourceHandler
        [] 0 0 1 4)
      (crepPcCompactTargetEvaluator [] skipNatCrepPrimitive skipNatFfi
        skipNatSharedMem 0 0 4)
      skipNatCodeRel skipNatExcpRel skipNatExceptionCode skipNatGlobalsLookup
      (.raise "E" (SourceWordExp.const 9).toExp) :=
  panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_raise_source_word
    "E" (SourceWordExp.const 9) skipNatCodeRel skipNatExcpRel
    skipNatExceptionCode skipNatGlobalsLookup [] [] skipNatPrimitive
    skipNatSourceHandler skipNatCrepPrimitive skipNatFfi skipNatSharedMem
    0 0 1 4 4 hbytesInWord hlookupSource hlookupException hfresh hexception
    hlookup hevidence

end Flapjack
