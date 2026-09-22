import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterWordRelation

/-!
Context-aware transport for adding a fresh one-word callee parameter.  The
extended context obligations are explicit, while the source/Crep state
transport is delegated to the established parameter theorem.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_add_word_parameter_fresh
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots)
    (hoverlap : panValueNoOverlap
      ((name, (.one, [slot])) :: context.vars))
    (hmax : panValueCtxtMax context.maxVar
      ((name, (.one, [slot])) :: context.vars)) :
    panValueCrepStateRelWithContext structs
      { context with vars := (name, (.one, [slot])) :: context.vars }
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  refine ⟨hoverlap, hmax, ?_⟩
  exact panValueCrepStateRel_add_word_parameter_fresh structs context
    sourceLocals sourceGlobals sourceMemory state name slot value hrel.2.2
    hname hfresh

end Flapjack
