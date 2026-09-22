import Flapjack.CrepeNestedDecsContextStability

namespace Flapjack.Test.CrepeNestedDecsContextStability

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem fresh_context_state_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) emptyContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := updateCrepLocalList (fun _ => none) [2, 3] [7, 9]
        memory := fun _ => none } := by
  apply panValueCrepStateRelWithContext_updateCrepLocalList_fresh
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    [2, 3] [7, 9]
  · refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  · rfl
  · intro name shape slots hlookup slot hslot
    simp [emptyContext, lookupInfo] at hlookup

#check @Flapjack.panValueCrepStateRelWithContext_updateCrepLocalList_fresh

end Flapjack.Test.CrepeNestedDecsContextStability
