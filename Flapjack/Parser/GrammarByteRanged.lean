import Flapjack.Parser.ConversionByteRanged

/-!
Byte-rangedness invariants for the PEG parser in `Flapjack/Parser/Grammar.lean`.

`parseTopDecs` lexes the source, runs the grammar to a `ParseTree`, and converts
it with `convTopDecList`.  The conversion lemmas in
`Flapjack/Parser/ConversionByteRanged.lean` show that a byte-ranged tree yields
byte-ranged declarations, so what remains is to show that the grammar only ever
builds trees whose leaves carry byte-ranged token payloads.

This module sets up the two invariants (`ToksByteRanged` on the remaining token
list, `TreesByteRanged` on a grammar result) and proves the primitive
combinators safe.  The per-rule grammar induction is left to the follow-up
slice; nothing here is `@[hol]`-tagged (the parser is Flapjack-specific
production infrastructure).
-/

namespace Flapjack.Parser

/-- Every token left in a parser state has a byte-ranged payload. -/
def ToksByteRanged (toks : Toks) : Prop := ∀ p ∈ toks, TokenNameByteRanged p.1

/-- Every tree in a grammar result has byte-ranged leaves. -/
def TreesByteRanged (trees : P.Trees) : Prop := ∀ t ∈ trees, ParseTreeByteRanged t

theorem ToksByteRanged.tail {t : Token × Locs} {rest : Toks}
    (h : ToksByteRanged (t :: rest)) : ToksByteRanged rest :=
  fun p hp => h p (by simp [hp])

theorem ToksByteRanged.cons {t : Token × Locs} {rest : Toks}
    (ht : TokenNameByteRanged t.1) (hr : ToksByteRanged rest) : ToksByteRanged (t :: rest) := by
  intro p hp
  rw [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ht
  · exact hr p hp

theorem TreesByteRanged.nil : TreesByteRanged ([] : P.Trees) := by
  intro t ht; simp at ht

theorem TreesByteRanged.append {a b : P.Trees}
    (ha : TreesByteRanged a) (hb : TreesByteRanged b) : TreesByteRanged (a ++ b) := by
  intro t ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · exact ha t ht
  · exact hb t ht

theorem TreesByteRanged.singleton {t : ParseTree} (h : ParseTreeByteRanged t) :
    TreesByteRanged [t] := by
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  exact h

theorem ParseTreeByteRanged.lf_iff {token : Token} {locs : Locs} :
    ParseTreeByteRanged (.lf token locs) ↔ TokenNameByteRanged token := by
  simp [ParseTreeByteRanged]

theorem mkLeaf_byteRanged {entry : Token × Locs} (h : TokenNameByteRanged entry.1) :
    TreesByteRanged (P.mkLeaf entry) := by
  apply TreesByteRanged.singleton
  exact ParseTreeByteRanged.lf_iff.mpr h

theorem defaultLeaf_trees_byteRanged {token : Token} (h : TokenNameByteRanged token) :
    ∀ s trees s', P.defaultLeaf token s = (some trees, s') → TreesByteRanged trees := by
  intro s trees s' hs
  change (some (P.mkLeaf (token, unknownLoc)), s) = (some trees, s') at hs
  simp only [Prod.mk.injEq, Option.some.injEq] at hs
  rw [← hs.1]
  exact mkLeaf_byteRanged h

/-- A parser computation that never breaks the token invariant. -/
def PStateToksSafe (p : P α) : Prop :=
  (∀ s a s', p s = (some a, s') → ToksByteRanged s.toks → ToksByteRanged s'.toks) ∧
  (∀ s s', p s = (none, s') → ToksByteRanged s.toks → ToksByteRanged s'.toks)

theorem PStateToksSafe.pure' (a : α) : PStateToksSafe (P.pure' a) := by
  constructor
  · intro s a' s' hs h
    change (some a, s) = (some a', s') at hs
    simp only [Prod.mk.injEq, Option.some.injEq] at hs
    rw [← hs.2]; exact h
  · intro s s' hs _
    change (some a, s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem PStateToksSafe.fail (message : String) : PStateToksSafe (P.fail (α := α) message) := by
  constructor
  · intro s a s' hs _
    simp only [P.fail] at hs
    exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    simp only [P.fail, Prod.mk.injEq] at hs
    rw [← hs.2]; exact h

theorem PStateToksSafe.bind {p : P α} {f : α → P β}
    (hp : PStateToksSafe p) (hf : ∀ a, PStateToksSafe (f a)) : PStateToksSafe (P.bind' p f) := by
  constructor
  · intro s b s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      exact (hf a).1 s'' b s' hs (hp.1 s a s'' heq h)
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      exact (hf a).2 s'' s' hs (hp.1 s a s'' heq h)
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h

theorem PStateToksSafe.orElse' {p q : P α}
    (hp : PStateToksSafe p) (hq : PStateToksSafe q) : PStateToksSafe (P.orElse' p q) := by
  constructor
  · intro s a s' hs h
    simp only [P.orElse'] at hs
    split at hs
    · rename_i a' s'' heq
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨_, h2⟩ := hs
      rw [← h2]
      exact hp.1 s a' s'' heq h
    · rename_i s'' heq
      exact hq.1 (s''.rewind s) a s' hs h
  · intro s s' hs h
    simp only [P.orElse'] at hs
    split at hs
    · rename_i a' s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
    · rename_i s'' heq
      exact hq.2 (s''.rewind s) s' hs h

theorem PStateToksSafe.choiceL : ∀ {l : List (P α)}, (∀ p ∈ l, PStateToksSafe p) →
    PStateToksSafe (P.choiceL l)
  | [], _ => by
      constructor
      · intro s a s' hs _
        exact absurd (congrArg Prod.fst hs) (by simp [P.choiceL])
      · intro s s' hs h
        change (none, s) = (none, s') at hs
        simp only [Prod.mk.injEq] at hs
        rw [← hs.2]; exact h
  | p :: ps, h => by
      simp only [P.choiceL]
      exact PStateToksSafe.orElse' (h p (by simp))
        (PStateToksSafe.choiceL (fun q hq => h q (by simp [hq])))

theorem PStateToksSafe.pegF {p : P α} {f : α → P β}
    (hp : PStateToksSafe p) (hf : ∀ a, PStateToksSafe (f a)) : PStateToksSafe (P.pegF p f) := by
  constructor
  · intro s b s' hs h
    simp only [P.pegF] at hs
    split at hs
    · rename_i a s'' heq
      exact (hf a).1 s'' b s' hs (hp.1 s a s'' heq h)
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h
  · intro s s' hs h
    simp only [P.pegF] at hs
    split at hs
    · rename_i a s'' heq
      exact (hf a).2 s'' s' hs (hp.1 s a s'' heq h)
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h

theorem PStateToksSafe.seqList : ∀ {l : List (P (List α))}, (∀ p ∈ l, PStateToksSafe p) →
    PStateToksSafe (P.seqList l)
  | [], _ => PStateToksSafe.pure' ([] : List α)
  | p :: ps, h => by
      simp only [P.seqList]
      exact PStateToksSafe.pegF (h p (by simp))
        (fun _ => PStateToksSafe.pegF (PStateToksSafe.seqList (fun q hq => h q (by simp [hq])))
          (fun _ => PStateToksSafe.pure' _))

theorem PStateToksSafe.optional' {p : P α} (hp : PStateToksSafe p) :
    PStateToksSafe (P.optional' p) := by
  constructor
  · intro s a s' hs h
    simp only [P.optional'] at hs
    split at hs
    · rename_i a' s'' heq
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨_, h2⟩ := hs
      rw [← h2]
      exact hp.1 s a' s'' heq h
    · simp only [Prod.mk.injEq, Option.some.injEq] at hs
      rw [← hs.2]
      exact h
  · intro s s' hs h
    simp only [P.optional'] at hs
    split at hs
    · exact absurd (congrArg Prod.fst hs) (by simp)
    · exact absurd (congrArg Prod.fst hs) (by simp)

theorem PStateToksSafe.expect (expected : Token) (described : String) :
    PStateToksSafe (P.expect expected described) := by
  constructor
  · intro s u s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [P.expect, hst] at hs
      simp only [P.fail, Prod.mk.injEq] at hs
      exact absurd hs.1 (by simp)
    | cons entry rest =>
      cases entry with
      | mk token locs =>
        simp only [P.expect, hst, PState.pop] at hs
        by_cases hc : token == expected
        · rw [if_pos hc] at hs
          simp only [Prod.mk.injEq] at hs
          rw [← hs.2]
          rw [hst] at h
          exact ToksByteRanged.tail h
        · rw [if_neg hc] at hs
          simp only [P.fail, Prod.mk.injEq] at hs
          exact absurd hs.1 (by simp)
  · intro s s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [P.expect, hst] at hs
      simp only [P.fail, Prod.mk.injEq] at hs
      rw [← hs.2]; exact h
    | cons entry rest =>
      cases entry with
      | mk token locs =>
        simp only [P.expect, hst, PState.pop] at hs
        by_cases hc : token == expected
        · rw [if_pos hc] at hs
          exact absurd (congrArg Prod.fst hs) (by simp)
        · rw [if_neg hc] at hs
          simp only [P.fail, Prod.mk.injEq] at hs
          rw [← hs.2]; exact h

theorem PStateToksSafe.advance : PStateToksSafe (P.advance) := by
  constructor
  · intro s u s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [P.advance, hst] at hs
      simp only [P.fail, Prod.mk.injEq] at hs
      exact absurd hs.1 (by simp)
    | cons entry rest =>
      cases entry with
      | mk token locs =>
        simp only [P.advance, hst, PState.pop] at hs
        simp only [Prod.mk.injEq] at hs
        rw [← hs.2]
        rw [hst] at h
        exact ToksByteRanged.tail h
  · intro s s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [P.advance, hst] at hs
      simp only [P.fail, Prod.mk.injEq] at hs
      rw [← hs.2]; exact h
    | cons entry rest =>
      cases entry with
      | mk token locs =>
        simp only [P.advance, hst] at hs
        exact absurd (congrArg Prod.fst hs) (by simp)

theorem PStateToksSafe.peek : PStateToksSafe (P.peek) := by
  constructor
  · intro s a s' hs h
    change (some (s.toks.head?.map Prod.fst), s) = (some a, s') at hs
    simp only [Prod.mk.injEq] at hs
    rw [← hs.2]; exact h
  · intro s s' hs _
    change (some (s.toks.head?.map Prod.fst), s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem PStateToksSafe.currentLocs : PStateToksSafe (P.currentLocs) := by
  constructor
  · intro s a s' hs h
    change (some (match s.toks with
        | [] => { start := Posn.eofPt, stop := Posn.eofPt : Locs }
        | (_, locs) :: _ => locs), s) = (some a, s') at hs
    simp only [Prod.mk.injEq] at hs
    rw [← hs.2]; exact h
  · intro s s' hs _
    change (some (match s.toks with
        | [] => { start := Posn.eofPt, stop := Posn.eofPt : Locs }
        | (_, locs) :: _ => locs), s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem PStateToksSafe.atEnd : PStateToksSafe (P.atEnd) := by
  constructor
  · intro s a s' hs h
    change (some s.toks.isEmpty, s) = (some a, s') at hs
    simp only [Prod.mk.injEq] at hs
    rw [← hs.2]; exact h
  · intro s s' hs _
    change (some s.toks.isEmpty, s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

end Flapjack.Parser
