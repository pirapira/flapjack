import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterListRelation

/-!
Context-aware generic callee parameter-list transport.  The list theorem
provides source/Crep state correspondence; this wrapper exposes the final
context well-formedness obligations at the same boundary.
-/

namespace Flapjack

theorem panValueCrepCalleeStateRelWithContext_parameters_append
    [OfNat α 0] [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hfresh : CalleeParameterListFreshAppend structs context parameters)
    (hoverlap : panValueNoOverlap
      (foldCalleeParameterContextAppend context parameters).vars)
    (hmax : panValueCtxtMax
      (foldCalleeParameterContextAppend context parameters).maxVar
      (foldCalleeParameterContextAppend context parameters).vars) :
    panValueCrepStateRelWithContext structs
      (foldCalleeParameterContextAppend context parameters)
      (foldCalleeParameterSource (fun _ => none) parameters) sourceGlobals
      sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none) parameters,
        memory := crepMemory } := by
  refine ⟨hoverlap, hmax, ?_⟩
  exact panValueCrepCalleeStateRel_parameters_append structs context
    sourceGlobals sourceMemory crepMemory parameters hglobals hmemory hfresh

end Flapjack
