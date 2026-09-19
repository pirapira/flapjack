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

end Flapjack
