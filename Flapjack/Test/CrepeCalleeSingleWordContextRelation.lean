import Flapjack.CrepeCalleeSingleWordContextRelation

namespace Flapjack.Test.CrepeCalleeSingleWordContextRelation

open Flapjack

def baseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 2, bytesInWord := 8 }

def oneWordContext : CompileContext Nat :=
  { baseContext with vars := [("x", (.one, [2]))] }

theorem callee_single_word_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) oneWordContext
      (updatePanValueMap (fun _ => none) "x" (.word 7)) (fun _ => none)
      (fun _ => none)
      { locals := updateCrepLocal (fun _ => none) 2 7
        memory := fun _ => none } := by
  apply panValueCrepCalleeStateRelWithContext_single_word
    ([] : StructContext) baseContext (fun _ => none) (fun _ => none)
    (fun _ => none) "x" 2 7
  · rfl
  · rfl
  · simp [baseContext, lookupInfo]
  · intro oldName oldShape oldSlots hne hlookup
    simp [baseContext, lookupInfo] at hlookup
  · refine ⟨?_, ?_⟩
    · simp [baseContext, lookupInfo]
    · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
      have hname : name = "x" := by
        by_cases hne : name = "x"
        · exact hne
        · simp [baseContext, lookupInfo, Ne.symm hne] at hlookup
      have hname' : name' = "x" := by
        by_cases hne : name' = "x"
        · exact hne
        · simp [baseContext, lookupInfo, Ne.symm hne] at hlookup'
      exact hname.trans hname'.symm
  · refine ⟨by omega, ?_⟩
    intro name shape slots hlookup slot hslot
    have hname : name = "x" := by
      by_cases hne : name = "x"
      · exact hne
      · simp [baseContext, lookupInfo, Ne.symm hne] at hlookup
    subst name
    have hpair : (Shape.one, [2]) = (shape, slots) := by
      simpa [baseContext, lookupInfo] using hlookup
    have hslots : [2] = slots := congrArg Prod.snd hpair
    rw [← hslots] at hslot
    simp at hslot
    change slot ≤ 2
    omega

#check @Flapjack.panValueCrepCalleeStateRelWithContext_single_word

end Flapjack.Test.CrepeCalleeSingleWordContextRelation
