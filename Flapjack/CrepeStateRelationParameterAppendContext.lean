import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterAppendRelation

/-!
Context-aware transport for appending one arbitrary structured callee
parameter.  The parameter-shape and flattened-local proof remains in the
existing append relation; this wrapper carries the target context invariants.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_add_parameter_append_fresh
    [OfNat α 0] [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (parameter : CalleeParameter α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hname : lookupInfo parameter.name context.vars = none)
    (hshape : panShapeMatches (panValueShape structs parameter.value)
      parameter.shape = true)
    (hlength : parameter.slots.length = parameter.values.length)
    (hdistinct : CrepDistinctNames parameter.slots)
    (hflat : panValueFlatWords parameter.value = parameter.values)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ parameter.name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ parameter.slots, slot ∉ oldSlots)
    (hoverlap : panValueNoOverlap
      (addCalleeParameterContextAppend context parameter).vars)
    (hmax : panValueCtxtMax context.maxVar
      (addCalleeParameterContextAppend context parameter).vars) :
    panValueCrepStateRelWithContext structs
      (addCalleeParameterContextAppend context parameter)
      (updatePanValueMap sourceLocals parameter.name parameter.value)
      sourceGlobals sourceMemory
      { state with
          locals := updateCrepLocalList state.locals parameter.slots parameter.values } := by
  refine ⟨hoverlap, hmax, ?_⟩
  exact panValueCrepStateRel_add_parameter_append_fresh structs context
    sourceLocals sourceGlobals sourceMemory state parameter hrel.2.2 hname
    hshape hlength hdistinct hflat hnoalias

end Flapjack
