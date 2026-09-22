import Flapjack.CrepeControlRelationContext

namespace Flapjack.Test.CrepeControlRelationContext

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

theorem normal_control_context_fixture :
    panValueCrepControlRelWithContext ([] : StructContext) emptyContext
      (fun _ _ _ => True)
      (.normal (fun _ => none) (fun _ => none) (fun _ => none))
      (.normal { locals := fun _ => none, memory := fun _ => none }) := by
  apply panValueCrepControlRelWithContext_normal
  refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega), ?_⟩
  exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩

#check @Flapjack.panValueCrepControlRelWithContext_normal
#check @Flapjack.panValueCrepControlRelWithContext_returned
#check @Flapjack.panValueCrepControlRelWithContext_raised

end Flapjack.Test.CrepeControlRelationContext
