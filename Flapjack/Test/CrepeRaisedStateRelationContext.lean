import Flapjack.CrepeRaisedStateRelationContext

namespace Flapjack.Test.CrepeRaisedStateRelationContext

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem raised_two_word_spill_context_fixture :
    panValueCrepRaisedStateRelExceptWithContext ([] : StructContext)
      emptyContext (fun _ => none) (fun _ => none)
      { locals := fun _ => none
        memory := updateMemory (updateMemory (fun _ => none) 4 7) 12 9 }
      (fun address => address = 4 ∨ address = 12) := by
  apply panValueCrepRaisedStateRelExceptWithContext_two_word_spill
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    4 8 7 9
  refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
  exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩

#check @Flapjack.panValueCrepRaisedStateRelExceptWithContext_two_word_spill

end Flapjack.Test.CrepeRaisedStateRelationContext
