import Flapjack.CrepeStateRelationMemoryUpdateContext

namespace Flapjack.Test.CrepeStateRelationMemoryUpdateContext

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem memory_word_update_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) emptyContext
      (fun _ => none) (fun _ => none)
      (updatePanValueMemory (fun _ => none) 4 (.word 7))
      { locals := fun _ => none,
        memory := updateMemory (fun _ => none) 4 7 } := by
  apply panValueCrepStateRelWithContext_update_memory_word
    ([] : StructContext) emptyContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none } 4 7
  · refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩

#check @Flapjack.panValueCrepStateRel_update_memory_word
#check @Flapjack.panValueCrepStateRelWithContext_update_memory_word

end Flapjack.Test.CrepeStateRelationMemoryUpdateContext
