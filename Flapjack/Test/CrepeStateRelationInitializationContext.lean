import Flapjack.CrepeStateRelationInitializationContext

namespace Flapjack.Test.CrepeStateRelationInitializationContext

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem initialize_context_state_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) emptyContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := initializeCrepLocals (fun _ => none) [2, 3]
        memory := fun _ => none } := by
  apply panValueCrepStateRelWithContext_initialize
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    "tmp" [2, 3]
  · refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  · simp [emptyContext, lookupInfo]
  · intro oldName oldShape oldSlots hne hlookup temporary htemporary
    simp [emptyContext, lookupInfo] at hlookup

#check @Flapjack.panValueCrepStateRelWithContext_initialize

end Flapjack.Test.CrepeStateRelationInitializationContext
