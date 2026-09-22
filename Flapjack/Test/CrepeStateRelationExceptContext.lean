import Flapjack.CrepeStateRelationExceptContext

namespace Flapjack.Test.CrepeStateRelationExceptContext

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem excluded_memory_context_fixture :
    panValueCrepStateRelExceptWithContext ([] : StructContext) emptyContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := fun _ => none,
        memory := updateMemory (fun _ => none) 4 7 }
      (fun address => address = 4) := by
  apply panValueCrepStateRelExceptWithContext_update_crep_at_excluded
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none } 4 7
    (fun address => address = 4)
  · refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  · rfl

theorem excluded_memory_context_second_write_fixture :
    panValueCrepStateRelExceptWithContext ([] : StructContext) emptyContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := fun _ => none,
        memory := updateMemory (updateMemory (fun _ => none) 4 7) 12 9 }
      (fun address => address = 4 ∨ address = 12) := by
  have hbase : panValueCrepStateRelWithContext ([] : StructContext)
      emptyContext (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := fun _ => none, memory := fun _ => none } := by
    refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  have hfirst := panValueCrepStateRelExceptWithContext_update_crep_at_excluded
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none } 4 7
    (fun address => address = 4 ∨ address = 12) hbase (Or.inl rfl)
  exact panValueCrepStateRelExceptWithContext_update_crep_at_excluded_again
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none)
    { locals := fun _ => none, memory := updateMemory (fun _ => none) 4 7 }
    12 9 (fun address => address = 4 ∨ address = 12) hfirst (Or.inr rfl)


theorem excluded_memory_context_projection_fixture :
    panValueCrepStateRelExcept [] emptyContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := (fun _ => none),
        memory := updateMemory (updateMemory (fun _ => none) 4 7) 12 9 }
      (fun address => address = 4 ∨ address = 12) := by
  apply panValueCrepStateRelExceptWithContext_to_stateRelExcept
  exact excluded_memory_context_second_write_fixture

#check @Flapjack.panValueCrepStateRelExceptWithContext_of_state_rel
#check @Flapjack.panValueCrepStateRelExceptWithContext_update_crep_at_excluded

#check @Flapjack.panValueCrepStateRelExceptWithContext_update_crep_at_excluded_again
#check @Flapjack.panValueCrepStateRelExceptWithContext_to_stateRelExcept
end Flapjack.Test.CrepeStateRelationExceptContext
