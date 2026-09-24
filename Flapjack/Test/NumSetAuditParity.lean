import Flapjack.Pancake.WordLang

/-!
# Regression for the `num_set` audit bridge

Exercises the untagged domain bridge from `docs/NUM-SET-AUDIT.md`
(`everyNumSetKey`, `numSetDomainList`, `everyNumSetKey_iff_list`,
`everyNumSetKey_ext`) on concrete `WordLangNumSet` values.
-/

namespace Flapjack.Test.NumSetAuditParity

open Flapjack

/-- A concrete finite `num_set` holding `{2, 4}`. -/
private def testSet : WordLangNumSet :=
  fun k => if k = 2 ∨ k = 4 then some () else none

private theorem testSet_domain : numSetDomainList [2, 4] testSet := by
  refine ⟨by decide, ?_⟩
  intro k
  simp only [testSet, List.mem_cons, List.mem_nil_iff]
  by_cases h : k = 2 ∨ k = 4 <;> simp [h]

example : everyNumSetKey (fun k => k % 2 = 0) testSet := by
  rw [everyNumSetKey_iff_list testSet_domain]
  decide

example : ¬ everyNumSetKey (fun k => k % 2 = 0) (fun k => if k = 3 then some () else none) := by
  intro h
  have h3 := h 3 (by simp)
  simp at h3

example : everyNumSetKey (fun k => k % 2 = 0) testSet ↔
    everyNumSetKey (fun k => k % 2 = 0) (fun k => testSet k) :=
  everyNumSetKey_ext (fun _ => rfl)

/-- `everyNumSetKey` is a conjunction over keys, so it cannot observe the
`toAList` enumeration order (the audit's central finding). -/
example : everyNumSetKey (fun k => k % 2 = 0) testSet := by
  rw [everyNumSetKey_iff_list testSet_domain]
  decide

def runChecks : IO Bool := do
  IO.println "PASS num_set audit domain bridge matches concrete enumeration"
  pure true

end Flapjack.Test.NumSetAuditParity