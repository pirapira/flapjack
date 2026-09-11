import Flapjack.CrepeStateRelation

/-!
State-level transport for a one-word local update.

Call correctness repeatedly updates a source binding and its corresponding
Crep slot while preserving globals and memory.  This wrapper exposes that
operation directly from the established local relation.
-/

namespace Flapjack

theorem panValueCrepStateRel_update_word
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  exact panValueCrepLocalsRel_update_word structs context sourceLocals
    state.locals name slot value hrel.2.1 hlookup hnoalias

end Flapjack
