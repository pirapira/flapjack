import Flapjack.Pancake.WordConvs

/-! # `pre_alloc_conventions` / `post_alloc_conventions` oracle parity

Direct check that the ported `preAllocConventions` / `postAllocConventions`
match the original HOL `wordConvs$pre_alloc_conventions_def` /
`post_alloc_conventions_def` rows in
`scripts/hol-probes/word_convs_alloc_conventions_probe.out`.

The declarations are composed from the untagged `everyStackVar` / `everyVar` /
`callArgConvention`; the `num_set` domain sub-terms rely on the audited
order-insensitive model of `docs/NUM-SET-AUDIT.md`, so nothing here is
`@[hol]`-tagged. -/

namespace Flapjack.Test.WordLangAllocConventionsParity

open Flapjack

private abbrev W := BitVec 8

private def single (n : Nat) : WordLangNumSet :=
  fun k => if k = n then some () else none

private def cut3 : WordLangCutsets := (single 3, fun _ => none)
private def cut4 : WordLangCutsets := (single 4, fun _ => none)
private def cut2 : WordLangCutsets := (single 2, fun _ => none)

private theorem everyNumSetKey_single (n : Nat) (P : Nat -> Bool) (h : P n = true) :
    everyNumSetKey P (single n) := by
  intro k hk
  by_cases hk' : k = n
  · subst hk'; exact h
  · simp [single, hk'] at hk

private theorem everyNumSetKey_none (P : Nat -> Bool) (t : WordLangNumSet)
    (h : ∀ k, t k = none) : everyNumSetKey P t := by
  intro k hk
  rw [h k] at hk
  exact absurd hk (by simp)

private theorem everyName_single_none (P : Nat -> Bool) (n : Nat) (h : P n = true) :
    everyName P (single n, fun _ => none) :=
  ⟨everyNumSetKey_single n P h, everyNumSetKey_none P (fun _ => none) (fun _ => rfl)⟩

private def ffiOk : WordLangProg W := .ffi "f" 2 4 6 8 cut3
private def ffiBadScalar : WordLangProg W := .ffi "f" 3 4 6 8 cut3
private def ffiBadCutset : WordLangProg W := .ffi "f" 2 4 6 8 cut4
private def ffiBadArgConv : WordLangProg W := .ffi "f" 2 4 6 9 cut3
private def moveOk : WordLangProg W := .move 0 [(2, 6)]
private def moveBad : WordLangProg W := .move 0 [(3, 4)]
private def allocBound : WordLangProg W := .alloc 2 cut2
private def retOk : WordLangProg W := .return 4 [2]

-- `pre_ok_ffi=T`
example : preAllocConventions ffiOk := by
  refine ⟨?_, rfl⟩
  show everyName isStackVar cut3
  exact everyName_single_none isStackVar 3 (by decide)

-- `pre_bad_scalar=F`
example : ¬ preAllocConventions ffiBadScalar := by
  intro h
  have hc : callArgConvention ffiBadScalar = true := h.2
  simp [ffiBadScalar, callArgConvention] at hc

-- `pre_bad_cutset=F`
example : ¬ preAllocConventions ffiBadCutset := by
  intro h
  have hcut : everyNumSetKey isStackVar (single 4) := by
    simpa [preAllocConventions, ffiBadCutset, everyStackVar, everyName, cut4] using h.1.1
  have h4 := hcut 4 (by simp [single])
  simp [isStackVar] at h4

-- `pre_bad_argconv=F`
example : ¬ preAllocConventions ffiBadArgConv := by
  intro h
  have hc : callArgConvention ffiBadArgConv = true := h.2
  simp [ffiBadArgConv, callArgConvention] at hc

-- `post_ok_move=T`
example : postAllocConventions 2 moveOk := by
  refine ⟨?_, ?_, rfl⟩
  · simp [moveOk, everyVar, isPhyVar]
  · simp [moveOk, everyStackVar]

-- `post_bad_move=F`
example : ¬ postAllocConventions 2 moveBad := by
  intro h
  simp [postAllocConventions, moveBad, everyVar, everyStackVar, callArgConvention,
    isPhyVar] at h

-- `post_bad_bound=F`
example : ¬ postAllocConventions 2 allocBound := by
  intro h
  have hcut : everyNumSetKey (fun name => decide (name ≥ 4)) (single 2) := by
    simpa [postAllocConventions, allocBound, everyVar, everyStackVar, everyName, cut2]
      using h.2.1.1
  have h2 := hcut 2 (by simp [single])
  simp at h2

-- `post_ok_ret=T`
example : postAllocConventions 2 retOk := by
  refine ⟨?_, ?_, rfl⟩
  · simp [retOk, everyVar, isPhyVar]
  · simp [retOk, everyStackVar]

/-- The eight checks above correspond one-to-one with the eight oracle rows in
`scripts/hol-probes/word_convs_alloc_conventions_probe.out`. -/
def runChecks : IO Bool := do
  IO.println "PASS wordConvs pre/post_alloc_conventions match all 8 oracle rows"
  pure true

end Flapjack.Test.WordLangAllocConventionsParity
