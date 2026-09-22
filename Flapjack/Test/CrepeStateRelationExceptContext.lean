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

#check @Flapjack.panValueCrepStateRelExceptWithContext_of_state_rel
#check @Flapjack.panValueCrepStateRelExceptWithContext_update_crep_at_excluded

end Flapjack.Test.CrepeStateRelationExceptContext
