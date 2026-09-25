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



/-! ### Tree-producing primitives

`PTreesSafe` is the tree-carrying analogue of `PStateToksSafe`: a parser that,
run on byte-ranged tokens, returns byte-ranged trees and leaves byte-ranged
tokens.  The grammar rules are built from these primitives, so proving them
safe is the base case of the per-rule induction. -/

theorem ToksByteRanged.head {entry : Token × Locs} {rest : Toks}
    (h : ToksByteRanged (entry :: rest)) : TokenNameByteRanged entry.1 :=
  h entry (by simp)

/-- A tree-producing parser that preserves byte-rangedness. -/
def PTreesSafe (p : P P.Trees) : Prop :=
  (∀ s trees s', p s = (some trees, s') → ToksByteRanged s.toks →
      TreesByteRanged trees ∧ ToksByteRanged s'.toks) ∧
  (∀ s s', p s = (none, s') → ToksByteRanged s.toks → ToksByteRanged s'.toks)

theorem PTreesSafe.pure (trees : P.Trees) (h : TreesByteRanged trees) :
    PTreesSafe (P.pure' trees) := by
  constructor
  · intro s trees' s' hs ht
    change (some trees, s) = (some trees', s') at hs
    simp only [Prod.mk.injEq, Option.some.injEq] at hs
    rw [← hs.1, ← hs.2]
    exact ⟨h, ht⟩
  · intro s s' hs _
    change (some trees, s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem PTreesSafe.bind {p : P P.Trees} {f : P.Trees → P P.Trees}
    (hp : PTreesSafe p) (hf : ∀ trees, TreesByteRanged trees → PTreesSafe (f trees)) :
    PTreesSafe (P.bind' p f) := by
  constructor
  · intro s trees s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i trees' s'' heq
      obtain ⟨ht, htoks⟩ := hp.1 s trees' s'' heq h
      exact (hf trees' ht).1 s'' trees s' hs htoks
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i trees' s'' heq
      obtain ⟨ht, htoks⟩ := hp.1 s trees' s'' heq h
      exact (hf trees' ht).2 s'' s' hs htoks
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h

theorem PTreesSafe.orElse' {p q : P P.Trees}
    (hp : PTreesSafe p) (hq : PTreesSafe q) : PTreesSafe (P.orElse' p q) := by
  constructor
  · intro s trees s' hs h
    simp only [P.orElse'] at hs
    split at hs
    · rename_i trees' s'' heq
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      rw [← h1, ← h2]
      exact hp.1 s trees' s'' heq h
    · rename_i s'' heq
      exact hq.1 (s''.rewind s) trees s' hs h
  · intro s s' hs h
    simp only [P.orElse'] at hs
    split at hs
    · rename_i trees' s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
    · rename_i s'' heq
      exact hq.2 (s''.rewind s) s' hs h

theorem keepTok_treesSafe (accept : Token → Bool) (described : String) :
    PTreesSafe (P.keepTok accept described) := by
  unfold PTreesSafe P.keepTok
  constructor
  · intro s trees s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [hst, P.fail, Prod.mk.injEq] at hs
      exact absurd hs.1 (by simp)
    | cons entry rest =>
      simp only [hst] at hs
      rw [hst] at h
      by_cases hacc : accept entry.1
      · rw [if_pos hacc] at hs
        simp only [Prod.mk.injEq, Option.some.injEq] at hs
        obtain ⟨h1, h2⟩ := hs
        rw [← h1, ← h2]
        exact ⟨mkLeaf_byteRanged (ToksByteRanged.head h), ToksByteRanged.tail h⟩
      · rw [if_neg hacc] at hs
        simp only [P.fail, Prod.mk.injEq] at hs
        exact absurd hs.1 (by simp)
  · intro s s' hs h
    cases hst : s.toks with
    | nil =>
      simp only [hst, P.fail, Prod.mk.injEq] at hs
      rw [← hs.2]
      rw [hst] at h
      exact h
    | cons entry rest =>
      simp only [hst] at hs
      by_cases hacc : accept entry.1
      · rw [if_pos hacc] at hs
        exact absurd (congrArg Prod.fst hs) (by simp)
      · rw [if_neg hacc] at hs
        simp only [P.fail, Prod.mk.injEq] at hs
        rw [← hs.2]; exact h

theorem keepExact_treesSafe (expected : Token) (described : String) :
    PTreesSafe (P.keepExact expected described) :=
  keepTok_treesSafe _ _

theorem keepKw_treesSafe (keyword : Keyword) (described : String) :
    PTreesSafe (P.keepKw keyword described) :=
  keepExact_treesSafe _ _

theorem keepIdent_treesSafe : PTreesSafe P.keepIdent := keepTok_treesSafe _ _
theorem keepFfiIdent_treesSafe : PTreesSafe P.keepFfiIdent := keepTok_treesSafe _ _
theorem keepInt_treesSafe : PTreesSafe P.keepInt := keepTok_treesSafe _ _
theorem keepNat_treesSafe : PTreesSafe P.keepNat := keepTok_treesSafe _ _
theorem keepAnnot_treesSafe : PTreesSafe P.keepAnnot := keepTok_treesSafe _ _

theorem defaultLeaf_treesSafe (token : Token) (h : TokenNameByteRanged token) :
    PTreesSafe (P.defaultLeaf token) := by
  unfold PTreesSafe P.defaultLeaf
  constructor
  · intro s trees s' hs ht
    change (some (P.mkLeaf (token, unknownLoc)), s) = (some trees, s') at hs
    simp only [Prod.mk.injEq, Option.some.injEq] at hs
    rw [← hs.1, ← hs.2]
    exact ⟨mkLeaf_byteRanged h, ht⟩
  · intro s s' hs _
    change (some (P.mkLeaf (token, unknownLoc)), s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem mkSubtree_treesByteRanged (nonterminal : Nonterminal) {children : P.Trees}
    (h : TreesByteRanged children) : TreesByteRanged (P.mkSubtree nonterminal children) := by
  apply TreesByteRanged.singleton
  unfold P.mkNode
  simp only [ParseTreeByteRanged]
  exact h

theorem emptyNode_treesSafe (nonterminal : Nonterminal) : PTreesSafe (P.emptyNode nonterminal) := by
  unfold PTreesSafe P.emptyNode
  constructor
  · intro s trees s' hs ht
    change (some [ParseTree.nd nonterminal [] unknownLoc], s) = (some trees, s') at hs
    simp only [Prod.mk.injEq, Option.some.injEq] at hs
    rw [← hs.1, ← hs.2]
    exact ⟨TreesByteRanged.singleton (by simp [ParseTreeByteRanged]), ht⟩
  · intro s s' hs _
    change (some [ParseTree.nd nonterminal [] unknownLoc], s) = (none, s') at hs
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem spanned_treesByteRanged {p : P P.Trees} (hp : PTreesSafe p) :
    ∀ s r s', P.spanned p s = (some r, s') → ToksByteRanged s.toks →
      TreesByteRanged r.1 ∧ ToksByteRanged s'.toks := by
  intro s r s' hs h
  unfold P.spanned at hs
  split at hs
  · rename_i children s'' heq
    obtain ⟨ht, htoks⟩ := hp.1 { s with lastConsumed := none } children s'' heq h
    simp only [Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨h1, h2⟩ := hs
    rw [← h1, ← h2]
    refine ⟨ht, ?_⟩
    cases hlast : s''.lastConsumed <;> simpa [hlast] using htoks
  · rename_i s'' heq
    exact absurd (congrArg Prod.fst hs) (by simp)

theorem spanned_failure_toks {p : P P.Trees} (hp : PTreesSafe p) {s s' : PState}
    (h : P.spanned p s = (none, s')) (ht : ToksByteRanged s.toks) : ToksByteRanged s'.toks := by
  unfold P.spanned at h
  split at h
  · rename_i v inner heq
    exact absurd (congrArg Prod.fst h) (by simp)
  · rename_i inner heq
    simp only [Prod.mk.injEq] at h
    rw [← h.2]
    exact hp.2 { s with lastConsumed := none } inner heq ht

theorem subtree_treesSafe (nonterminal : Nonterminal) {p : P P.Trees} (hp : PTreesSafe p) :
    PTreesSafe (P.subtree nonterminal p) := by
  constructor
  · intro s trees s' hs h
    unfold P.subtree at hs
    split at hs
    · rename_i children locs s'' heq
      obtain ⟨ht, htoks⟩ := spanned_treesByteRanged hp s (children, locs) s'' heq h
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      rw [← h1, ← h2]
      refine ⟨?_, htoks⟩
      apply TreesByteRanged.singleton
      simp only [ParseTreeByteRanged]
      exact ht
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    unfold P.subtree at hs
    split at hs
    · rename_i children locs s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact spanned_failure_toks hp heq h

theorem tryRule_treesSafe {p : P P.Trees} (hp : PTreesSafe p) :
    PTreesSafe (P.tryRule p) := by
  unfold P.tryRule
  exact PTreesSafe.orElse' hp (PTreesSafe.pure [] TreesByteRanged.nil)

end Flapjack.Parser
