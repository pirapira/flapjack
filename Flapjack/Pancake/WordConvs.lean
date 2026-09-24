import Flapjack.HolRef

/-!
# CakeML backend `wordConvs` syntactic conventions

Counterpart of `cakeml/compiler/backend/semantics/wordConvsScript.sml`.  This
module ports the label-preservation relation first; the remaining conventions
and `extract_labels` need the backend `wordLang$prog` model and land in
follow-up slices.

HOL's `set new_labs SUBSET set old_labs` is represented pointwise as
`∀ label, label ∈ newLabels → label ∈ oldLabels`, which is exactly set
inclusion and needs no `DecidableEq` instance; `ALL_DISTINCT` is `List.Nodup`.
-/

namespace Flapjack

/-- Exact source counterpart of CakeML `wordConvs$labels_rel_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:139-143`): labels may be
forgotten but not invented, and distinctness is preserved. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_def"]
def labelsRel (oldLabels newLabels : List β) : Prop :=
  (oldLabels.Nodup → newLabels.Nodup) ∧
    ∀ label, label ∈ newLabels → label ∈ oldLabels

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_refl"]
theorem labelsRel_refl (labels : List β) : labelsRel labels labels :=
  ⟨fun distinct => distinct, fun _ member => member⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_APPEND"]
theorem labelsRel_append {xs xs₁ ys ys₁ : List β}
    (hxs : labelsRel xs xs₁) (hys : labelsRel ys ys₁) :
    labelsRel (xs ++ ys) (xs₁ ++ ys₁) := by
  obtain ⟨hxsDistinct, hxsSubset⟩ := hxs
  obtain ⟨hysDistinct, hysSubset⟩ := hys
  refine ⟨?_, ?_⟩
  · intro hdistinct
    obtain ⟨hxsNodup, hysNodup, hdisjoint⟩ := List.nodup_append.mp hdistinct
    refine List.nodup_append.mpr ⟨hxsDistinct hxsNodup, hysDistinct hysNodup, ?_⟩
    intro a inXs₁ b inYs₁ equal
    exact hdisjoint a (hxsSubset a inXs₁) b (hysSubset b inYs₁) equal
  · intro label member
    rw [List.mem_append] at member
    rw [List.mem_append]
    rcases member with member | member
    · exact Or.inl (hxsSubset label member)
    · exact Or.inr (hysSubset label member)

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_CONS"]
theorem labelsRel_cons {x x₁ : β} {ys ys₁ : List β}
    (hx : labelsRel [x] [x₁]) (hys : labelsRel ys ys₁) :
    labelsRel (x :: ys) (x₁ :: ys₁) := by
  simpa using labelsRel_append hx hys

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_TRANS"]
theorem labelsRel_trans {xs ys zs : List β}
    (hxy : labelsRel xs ys) (hyz : labelsRel ys zs) : labelsRel xs zs := by
  obtain ⟨hxyDistinct, hxySubset⟩ := hxy
  obtain ⟨hyzDistinct, hyzSubset⟩ := hyz
  exact ⟨fun distinct => hyzDistinct (hxyDistinct distinct),
    fun label member => hxySubset label (hyzSubset label member)⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "PERM_IMP_labels_rel"]
theorem labelsRel_of_perm {xs ys : List β} (hperm : xs.Perm ys) : labelsRel ys xs :=
  ⟨fun distinct => hperm.symm.nodup distinct, fun _ member => hperm.subset member⟩

end Flapjack