import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeStateRelationWordUpdate

/-!
Context-aware transport for a one-word source/Crep local update.  The
compiler context is unchanged, while the existing state relation supplies the
local binding and slot correspondence.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_update_word
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    panValueCrepStateRelWithContext structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRel_update_word structs context sourceLocals
    sourceGlobals sourceMemory state name slot value hrel.2.2 hlookup hnoalias

end Flapjack
