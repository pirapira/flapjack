import Flapjack.CrepeStateRelationSlotUpdateContext

namespace Flapjack.Test.CrepeStateRelationSlotUpdateContext

open Flapjack

def oneWordContext : CompileContext Nat :=
  { vars := [("x", (.one, [2]))], functions := [], exceptions := [],
    maxVar := 2, bytesInWord := 8 }

theorem update_slot_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) oneWordContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := updateCrepLocal (fun _ => none) 0 7
        memory := fun _ => none } := by
  apply panValueCrepStateRelWithContext_update_slot
    ([] : StructContext) oneWordContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none } 0 7
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [oneWordContext, lookupInfo]
      · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
        have hname : name = "x" := by
          by_cases hne : name = "x"
          · exact hne
          · simp [oneWordContext, lookupInfo, Ne.symm hne] at hlookup
        have hname' : name' = "x" := by
          by_cases hne : name' = "x"
          · exact hne
          · simp [oneWordContext, lookupInfo, Ne.symm hne] at hlookup'
        exact hname.trans hname'.symm
    · refine ⟨by omega, ?_⟩
      intro name shape slots hlookup slot hslot
      have hname : name = "x" := by
        by_cases hne : name = "x"
        · exact hne
        · simp [oneWordContext, lookupInfo, Ne.symm hne] at hlookup
      subst name
      have hpair : (Shape.one, [2]) = (shape, slots) := by
        simpa [oneWordContext, lookupInfo] using hlookup
      have hslots : [2] = slots := congrArg Prod.snd hpair
      rw [← hslots] at hslot
      simp at hslot
      change slot ≤ 2
      omega
    · exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  · intro oldName oldShape oldSlots hlookup htemporary
    have hname : oldName = "x" := by
      by_cases hne : oldName = "x"
      · exact hne
      · simp [oneWordContext, lookupInfo, Ne.symm hne] at hlookup
    subst oldName
    have hpair : (Shape.one, [2]) = (oldShape, oldSlots) := by
      simpa [oneWordContext, lookupInfo] using hlookup
    have hslots : [2] = oldSlots := congrArg Prod.snd hpair
    rw [← hslots] at htemporary
    simp at htemporary

#check @Flapjack.panValueCrepStateRelWithContext_update_slot

end Flapjack.Test.CrepeStateRelationSlotUpdateContext
