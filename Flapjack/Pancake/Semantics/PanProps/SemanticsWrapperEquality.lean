import Flapjack.Pancake.Semantics.PanProps.SemanticsWrapper

namespace Flapjack

/-- Monotone event traces under an `Incomplete`-only family form an `lprefixChain`
    Flapjack-specific proof infrastructure for the original event-prefix premises;
    it is not a separate HOL declaration. -/
private theorem panPropsSemanticsWrapper_chain
    (f : Nat → SemanticsRunResHOL HolOutcome × List HolIoEvent)
    (hinc : ∀ k, (f k).1 = .Incomplete)
    (hpre : ∀ k k' ev, f (k + k') = (.Incomplete, ev) →
      ∃ r' ev', f k = (r', ev') ∧ ev' <+: ev) :
    HolLList.lprefixChain (fun l => ∃ k, l = HolLList.fromList (f k).2) := by
  intro l1 l2 ⟨k1, e1⟩ ⟨k2, e2⟩
  subst e1; subst e2
  have mono : ∀ a b, a ≤ b → (f a).2 <+: (f b).2 := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨r', ev', he, hp⟩ := hpre a d (f (a + d)).2 (Prod.ext (hinc _) rfl)
    rw [he]; exact hp
  rcases Nat.le_total k1 k2 with h | h
  · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (mono _ _ h))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (mono _ _ h))

open Classical in
/-- Exact HOL `semantics_wrapper_eq` (`panPropsScript.sml:1831-1929`):
    all six curried premises and the equality conclusion are kept, over arbitrary
    `absf`/`concf`.  HOL `IS_PREFIX ev ev'` (`ev'` is a prefix of `ev`) is Lean
    `ev' <+: ev`.  No chain premise is added: the proof derives both prefix chains
    from the premises, as HOL does.  Because the equality is between two
    applications of the same `panPropsSemanticsWrapper` formula, it does not
    depend on which witnesses HOL `@`/Lean `Classical.choose` select (see the
    caveat on `panPropsSemanticsWrapper`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "semantics_wrapper_eq"]
theorem panPropsSemanticsWrapper_eq
    (absf concf : Nat → SemanticsRunResHOL HolOutcome × List HolIoEvent) :
    panPropsSemanticsWrapper absf ≠ .fail →
    (∀ k r ev, absf k = (r, ev) → r ≠ .RunError → ∃ k', concf (k + k') = (r, ev)) →
    (∀ k k' r ev, concf k = (r, ev) → r ≠ .Incomplete → concf (k + k') = (r, ev)) →
    (∀ k k' r ev, absf k = (r, ev) → r ≠ .Incomplete → absf (k + k') = (r, ev)) →
    (∀ k k' ev, absf (k + k') = (.Incomplete, ev) →
      ∃ r' ev', absf k = (r', ev') ∧ ev' <+: ev) →
    (∀ k k' ev, concf (k + k') = (.Incomplete, ev) →
      ∃ r' ev', concf k = (r', ev') ∧ ev' <+: ev) →
    panPropsSemanticsWrapper concf = panPropsSemanticsWrapper absf := by
  intro hfail h1 h2 _h3 h4 h5
  have hnoErrA : ¬ ∃ k v, absf k = (.RunError, v) := by
    intro h; apply hfail; unfold panPropsSemanticsWrapper; rw [if_pos h]
  cases hA : holOptionSome (fun res => ∃ k r ev,
      absf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
  | some res =>
    obtain ⟨ka, r, ev, hka, rfl⟩ := holOptionSome_some hA
    obtain ⟨k', hc⟩ := h1 ka _ _ hka (by intro h; cases h)
    have claim : ∀ k2 r2 v2, concf k2 = (r2, v2) →
        (r2, v2) = (.CompleteResult r, ev) ∨ r2 = .Incomplete := by
      intro k2 r2 v2 hk2
      by_cases hr2 : r2 = .Incomplete
      · exact Or.inr hr2
      left
      rcases Nat.le_total k2 (ka + k') with h | h
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
        have := h2 k2 d r2 v2 hk2 hr2
        rw [← hd, hc] at this; exact this.symm
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
        have := h2 (ka + k') d _ _ hc (by intro h; cases h)
        rw [← hd, hk2] at this; exact this
    have hnoErrC : ¬ ∃ k v, concf k = (.RunError, v) := by
      rintro ⟨k, v, hk⟩
      rcases claim k _ _ hk with h | h <;> cases h
    have hC : holOptionSome (fun res => ∃ k r ev,
        concf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) =
        some (HolBehaviour.terminate r ev) := by
      apply HolLList.holOptionSome_eq_some ⟨ka + k', r, ev, hc, rfl⟩
      rintro y ⟨k2, r2, v2, hk2, rfl⟩
      rcases claim k2 _ _ hk2 with h | h
      · cases h; rfl
      · cases h
    unfold panPropsSemanticsWrapper
    rw [if_neg hnoErrC, if_neg hnoErrA, hC, hA]
  | none =>
    have hnoCR : ∀ k r ev, absf k ≠ (.CompleteResult r, ev) := fun k r ev hk =>
      holOptionSome_none hA _ ⟨k, r, ev, hk, rfl⟩
    have hincA : ∀ k, (absf k).1 = .Incomplete := by
      intro k
      match hk : absf k with
      | (.RunError, v) => exact absurd ⟨k, v, hk⟩ hnoErrA
      | (.CompleteResult r, ev) => exact absurd hk (hnoCR k r ev)
      | (.Incomplete, _) => rfl
    have hpfx : ∀ k, ∃ k', concf (k + k') = (.Incomplete, (absf k).2) := fun k =>
      h1 k _ _ (Prod.ext (hincA k) rfl) (by intro h; cases h)
    have hincC : ∀ k, (concf k).1 = .Incomplete := by
      intro k
      by_cases hr : (concf k).1 = .Incomplete
      · exact hr
      obtain ⟨k', hk'⟩ := hpfx k
      have := h2 k k' _ _ (Prod.ext rfl rfl) hr
      rw [hk'] at this
      exact absurd (congrArg Prod.fst this).symm hr
    have hnoErrC : ¬ ∃ k v, concf k = (.RunError, v) := by
      rintro ⟨k, v, hk⟩
      have := hincC k; rw [hk] at this; cases this
    have hC : holOptionSome (fun res => ∃ k r ev,
        concf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) = none := by
      unfold holOptionSome
      rw [dif_neg]
      rintro ⟨_, k, r, ev, hk, _⟩
      have := hincC k; rw [hk] at this; cases this
    have cA := panPropsSemanticsWrapper_chain absf hincA h4
    have cC := panPropsSemanticsWrapper_chain concf hincC h5
    have hnth : ∀ n,
        HolLList.lprefixChainNth n (fun l => ∃ k, l = HolLList.fromList (concf k).2) =
        HolLList.lprefixChainNth n (fun l => ∃ k, l = HolLList.fromList (absf k).2) := by
      intro n
      unfold HolLList.lprefixChainNth
      congr 1
      funext x
      apply propext
      constructor
      · rintro ⟨l, ⟨k, rfl⟩, hl⟩
        refine ⟨_, ⟨k, rfl⟩, ?_⟩
        obtain ⟨k', hk'⟩ := hpfx k
        obtain ⟨r', ev', he, hp⟩ := h5 k k' _ hk'
        have hpre : (concf k).2 <+: (absf k).2 := by rw [he]; exact hp
        exact HolLList.lprefix_lnth ((HolLList.lprefix_fromList _ _).2 hpre) hl
      · rintro ⟨l, ⟨k, rfl⟩, hl⟩
        obtain ⟨k', hk'⟩ := hpfx k
        exact ⟨_, ⟨k + k', rfl⟩, by rw [hk']; exact hl⟩
    have hlub :
        HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (concf k).2) =
        HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (absf k).2) := by
      apply HolLList.ext_of_rep
      intro n
      rw [← HolLList.lnth_eq_rep, ← HolLList.lnth_eq_rep,
        HolLList.lnth_buildLprefixLub cC, HolLList.lnth_buildLprefixLub cA, hnth]
    unfold panPropsSemanticsWrapper
    rw [if_neg hnoErrC, if_neg hnoErrA, hC, hA, hlub]



end Flapjack
