import Flapjack.CrepeStateRelationWordUpdateContext

namespace Flapjack.Test.CrepeStateRelationWordUpdateContext

open Flapjack

def oneWordContext : CompileContext Nat :=
  { vars := [("x", (.one, [2]))], functions := [], exceptions := [],
    maxVar := 2, bytesInWord := 8 }

theorem update_word_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) oneWordContext
      (updatePanValueMap (fun _ => none) "x" (.word 7)) (fun _ => none) (fun _ => none)
      { locals := updateCrepLocal (fun _ => none) 2 7
        memory := fun _ => none } := by
  apply panValueCrepStateRelWithContext_update_word
    ([] : StructContext) oneWordContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    "x" 2 7
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
  · rfl
  · intro oldName oldShape oldSlots hne hlookup
    by_cases hname : oldName = "x"
    · subst oldName
      simp at hne
    · simp [oneWordContext, lookupInfo, Ne.symm hname] at hlookup

#check @Flapjack.panValueCrepStateRelWithContext_update_word

end Flapjack.Test.CrepeStateRelationWordUpdateContext
