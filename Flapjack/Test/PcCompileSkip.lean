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

end Flapjack
