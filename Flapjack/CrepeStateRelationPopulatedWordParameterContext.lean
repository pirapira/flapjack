import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterWordRelation

/-!
Context-aware transport for adding a one-word parameter when its target slot
already contains the value.  This packages the populated-slot call boundary
while keeping context well-formedness explicit.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_add_word_parameter
    [LawfulBEq String] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hslot : state.locals slot = some value)
    (hnoalias : ∀ oldName oldShape oldSlots,
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
  exact panValueCrepStateRel_add_word_parameter structs context sourceLocals
    sourceGlobals sourceMemory state name slot value hrel.2.2 hslot hnoalias

end Flapjack
