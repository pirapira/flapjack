import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterWordRelation

/-!
Context-aware transport for installing a fresh Crep local slot.  This is the
callee-parameter boundary where the source environment and memory stay fixed.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_update_slot
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (slot : Nat) (value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hfresh : ∀ oldName oldShape oldSlots,
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRel_update_slot structs context sourceLocals
    sourceGlobals sourceMemory state slot value hrel.2.2 hfresh

end Flapjack
