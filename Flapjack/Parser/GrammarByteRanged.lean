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

/-! `rpt` repeats a parser while it succeeds, so its result is a concatenation
    of tree-safety-respecting chunks.  `optional'` is the only primitive that
    returns an `Option`, so we record its own invariant and bind it. -/

/-- Tree-safety for a parser returning an optional tree list (the shape used
    inside `rpt`). -/
def POptionTreesSafe (p : P (Option P.Trees)) : Prop :=
  (∀ s o s', p s = (some o, s') → ToksByteRanged s.toks →
      (match o with
       | none => True
       | some trees => TreesByteRanged trees) ∧
        ToksByteRanged s'.toks) ∧
  (∀ s s', p s = (none, s') → ToksByteRanged s.toks → ToksByteRanged s'.toks)

theorem POptionTreesSafe.bind {p : P (Option P.Trees)} {f : Option P.Trees → P P.Trees}
    (hp : POptionTreesSafe p)
    (hf : ∀ o, (match o with
                | none => True
                | some trees => TreesByteRanged trees) → PTreesSafe (f o)) :
    PTreesSafe (P.bind' p f) := by
  constructor
  · intro s trees s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i o s'' heq
      have hp1 := hp.1 s o s'' heq h
      exact (hf o hp1.1).1 s'' trees s' hs hp1.2
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i o s'' heq
      have hp1 := hp.1 s o s'' heq h
      exact (hf o hp1.1).2 s'' s' hs hp1.2
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h

theorem optional'_optionTreesSafe {p : P P.Trees} (hp : PTreesSafe p) :
    POptionTreesSafe (P.optional' p) := by
  constructor
  · intro s o s' hs h
    simp only [P.optional'] at hs
    split at hs
    · rename_i trees s'' heq
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      subst h1
      rw [← h2]
      exact hp.1 s trees s'' heq h
    · rename_i s'' heq
      simp only [Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      subst h1
      rw [← h2]
      exact ⟨trivial, h⟩
  · intro s s' hs h
    simp only [P.optional'] at hs
    split at hs
    · rename_i trees s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)

theorem rpt_treesSafe {p : P P.Trees} (hp : PTreesSafe p) :
    ∀ steps, PTreesSafe (P.rpt p steps) := by
  intro steps
  induction steps with
  | zero =>
    rw [P.rpt]
    exact PTreesSafe.pure [] TreesByteRanged.nil
  | succ steps ih =>
    rw [P.rpt]
    exact POptionTreesSafe.bind (optional'_optionTreesSafe hp) (fun o ho => by
      cases o with
      | none => exact PTreesSafe.pure [] TreesByteRanged.nil
      | some trees =>
          exact PTreesSafe.bind ih (fun rest hrest =>
            PTreesSafe.pure (trees ++ rest) (TreesByteRanged.append ho hrest)))

theorem rptHere_treesSafe {p : P P.Trees} (hp : PTreesSafe p) :
    PTreesSafe (P.rptHere p) := by
  constructor
  · intro s trees s' hs h
    simp only [P.rptHere] at hs
    exact (rpt_treesSafe hp s.remaining).1 s trees s' hs h
  · intro s s' hs h
    simp only [P.rptHere] at hs
    exact (rpt_treesSafe hp s.remaining).2 s s' hs h

/-! ### Terminal and combinator rule safety (bead flapjack-0up.1)

The grammar's terminal-only rules and the `RetNT` rule are built purely from
`keepExact`/`keepIdent`/`consume`/`subtree`, all of which are already known
safe, so their byte-rangedness follows without the mutual fuel induction. -/

theorem PTreesSafe.of_stateSafe {α : Type} {p : P α} (hp : PStateToksSafe p) :
    PTreesSafe (P.bind' p (fun _ => P.pure' [])) := by
  constructor
  · intro s trees s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      have hp1 := hp.1 s a s'' heq h
      simp only [P.pure', Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨TreesByteRanged.nil, hp1⟩
    · rename_i s'' heq
      have hf := congrArg Prod.fst hs
      change (none : Option P.Trees) = some trees at hf
      simp at hf
  · intro s s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      have hf := congrArg Prod.fst hs
      change (some ([] : P.Trees)) = none at hf
      simp at hf
    · rename_i s'' heq
      have h2 : s'' = s' := congrArg Prod.snd hs
      rw [h2] at heq
      exact hp.2 s s' heq h

theorem consume_treesSafe (expected : Token) (described : String) :
    PTreesSafe (P.consume expected described) :=
  PTreesSafe.of_stateSafe (PStateToksSafe.expect expected described)

theorem consumeKw_treesSafe (keyword : Keyword) (described : String) :
    PTreesSafe (P.consumeKw keyword described) :=
  consume_treesSafe (.keywordT keyword) described

theorem PTreesSafe.consume_bind {q : P P.Trees} (hq : PTreesSafe q)
    (expected : Token) (described : String) :
    PTreesSafe (P.bind' (P.consume expected described) (fun _ => q)) :=
  PTreesSafe.bind (consume_treesSafe expected described) (fun _ _ => hq)

theorem gEqOps_treesSafe : PTreesSafe gEqOps := by
  unfold gEqOps
  exact PTreesSafe.orElse' (keepExact_treesSafe .eqT "==") (keepExact_treesSafe .neqT "!=")

theorem gCmpOps_treesSafe : PTreesSafe gCmpOps := by
  unfold gCmpOps
  repeat' apply PTreesSafe.orElse'
  all_goals exact keepExact_treesSafe _ _

theorem gShiftOps_treesSafe : PTreesSafe gShiftOps := by
  unfold gShiftOps
  repeat' apply PTreesSafe.orElse'
  all_goals exact keepExact_treesSafe _ _

theorem gAddOps_treesSafe : PTreesSafe gAddOps := by
  unfold gAddOps
  exact PTreesSafe.orElse' (keepExact_treesSafe .plusT "+") (keepExact_treesSafe .minusT "-")

theorem gMulOps_treesSafe : PTreesSafe gMulOps := by
  unfold gMulOps
  exact keepExact_treesSafe .starT "*"

theorem gRet_treesSafe : PTreesSafe gRet := by
  unfold gRet
  apply subtree_treesSafe
  exact PTreesSafe.bind keepIdent_treesSafe
    (fun name hname => PTreesSafe.consume_bind (PTreesSafe.pure name hname) .assignT "=")


theorem PTreesSafe.fail (message : String) :
    PTreesSafe (P.fail (α := P.Trees) message) :=
  PTreesSafe.of_stateSafe (α := P.Trees) (PStateToksSafe.fail (α := P.Trees) message)

set_option maxHeartbeats 2000000 in
theorem grammarBlock1_treesSafe :
    ∀ fuel, PTreesSafe (gShape fuel) ∧ PTreesSafe (gShapeComb fuel) ∧
      PTreesSafe (gShapedIdent fuel) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [gShape, gShapeComb, gShapedIdent] <;>
        exact PTreesSafe.fail fuelExhausted
    | succ m =>
      obtain ⟨hS, hC, hI⟩ := ih m (by omega)
      refine ⟨?_, ?_, ?_⟩
      · simp only [gShape]
        refine PTreesSafe.orElse' keepInt_treesSafe ?_
        refine PTreesSafe.orElse' ?_ keepIdent_treesSafe
        refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun open' ho => ?_)
        refine PTreesSafe.bind hC (fun inner hi => ?_)
        refine PTreesSafe.bind (consume_treesSafe .rCurT "}") (fun close hc => ?_)
        exact PTreesSafe.pure (open' ++ inner ++ close)
          (TreesByteRanged.append (TreesByteRanged.append ho hi) hc)
      · simp only [gShapeComb]
        refine subtree_treesSafe .shapeComb ?_
        refine PTreesSafe.bind hS (fun first hf => ?_)
        refine PTreesSafe.bind (rptHere_treesSafe (PTreesSafe.consume_bind hS .commaT ","))
          (fun rest hr => ?_)
        exact PTreesSafe.pure (first ++ rest) (TreesByteRanged.append hf hr)
      · simp only [gShapedIdent]
        refine PTreesSafe.orElse' ?_ ?_
        · refine PTreesSafe.bind hS (fun shape hs => ?_)
          refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
          exact PTreesSafe.pure (shape ++ name) (TreesByteRanged.append hs hn)
        · refine PTreesSafe.bind
            (defaultLeaf_treesSafe .defaultShT (by simp [TokenNameByteRanged]))
            (fun shape hs => ?_)
          refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
          exact PTreesSafe.pure (shape ++ name) (TreesByteRanged.append hs hn)

theorem gShape_treesSafe : ∀ fuel, PTreesSafe (gShape fuel) :=
  fun fuel => (grammarBlock1_treesSafe fuel).1

theorem gShapeComb_treesSafe : ∀ fuel, PTreesSafe (gShapeComb fuel) :=
  fun fuel => (grammarBlock1_treesSafe fuel).2.1

theorem gShapedIdent_treesSafe : ∀ fuel, PTreesSafe (gShapedIdent fuel) :=
  fun fuel => (grammarBlock1_treesSafe fuel).2.2

theorem gShapedIdentList_treesSafe (nonterminal : Nonterminal) (fuel : Nat) :
    PTreesSafe (gShapedIdentList nonterminal fuel) := by
  simp only [gShapedIdentList]
  refine subtree_treesSafe nonterminal ?_
  refine PTreesSafe.bind (gShapedIdent_treesSafe fuel) (fun first hf => ?_)
  refine PTreesSafe.bind
    (rptHere_treesSafe
      (PTreesSafe.consume_bind (gShapedIdent_treesSafe fuel) .commaT ","))
    (fun rest hr => ?_)
  exact PTreesSafe.pure (first ++ rest) (TreesByteRanged.append hf hr)


theorem subtree_rptBind_treesSafe (nt : Nonterminal) {gFirst gOps gTail : P P.Trees}
    (hFirst : PTreesSafe gFirst) (hOps : PTreesSafe gOps) (hTail : PTreesSafe gTail) :
    PTreesSafe (P.subtree nt (do
      let first ← gFirst
      let rest ← P.rptHere (do let _ ← gOps; gTail)
      pure (first ++ rest))) := by
  refine subtree_treesSafe nt ?_
  refine PTreesSafe.bind hFirst (fun first hf => ?_)
  refine PTreesSafe.bind (rptHere_treesSafe (PTreesSafe.bind hOps (fun _ _ => hTail))) (fun rest hr => ?_)
  exact PTreesSafe.pure (first ++ rest) (TreesByteRanged.append hf hr)

theorem subtree_rptChain_treesSafe (nt : Nonterminal) {gX gOps : P P.Trees}
    (hX : PTreesSafe gX) (hOps : PTreesSafe gOps) :
    PTreesSafe (P.subtree nt (do
      let first ← gX
      let rest ← P.rptHere (do let op ← gOps; let next ← gX; pure (op ++ next))
      pure (first ++ rest))) := by
  refine subtree_treesSafe nt ?_
  refine PTreesSafe.bind hX (fun first hf => ?_)
  refine PTreesSafe.bind (rptHere_treesSafe (PTreesSafe.bind hOps (fun op ho => PTreesSafe.bind hX (fun next hn => PTreesSafe.pure (op ++ next) (TreesByteRanged.append ho hn))))) (fun rest hr => ?_)
  exact PTreesSafe.pure (first ++ rest) (TreesByteRanged.append hf hr)

theorem subtree_tryChain_treesSafe (nt : Nonterminal) {gX gOps : P P.Trees}
    (hX : PTreesSafe gX) (hOps : PTreesSafe gOps) :
    PTreesSafe (P.subtree nt (do
      let first ← gX
      let rest ← P.tryRule (do let op ← gOps; let right ← gX; pure (op ++ right))
      pure (first ++ rest))) := by
  refine subtree_treesSafe nt ?_
  refine PTreesSafe.bind hX (fun first hf => ?_)
  refine PTreesSafe.bind (tryRule_treesSafe (PTreesSafe.bind hOps (fun op ho => PTreesSafe.bind hX (fun right hn => PTreesSafe.pure (op ++ right) (TreesByteRanged.append ho hn))))) (fun rest hr => ?_)
  exact PTreesSafe.pure (first ++ rest) (TreesByteRanged.append hf hr)

set_option maxHeartbeats 8000000 in
theorem grammarBlock2_treesSafe :
    ∀ fuel,
      PTreesSafe (gExp fuel) ∧ PTreesSafe (gEBoolAnd fuel) ∧
      PTreesSafe (gEEq fuel) ∧ PTreesSafe (gECmp fuel) ∧
      PTreesSafe (gELoad fuel) ∧ PTreesSafe (gELoadByte fuel) ∧
      PTreesSafe (gELoad32 fuel) ∧ PTreesSafe (gEOr fuel) ∧
      PTreesSafe (gEXor fuel) ∧ PTreesSafe (gEAnd fuel) ∧
      PTreesSafe (gEShift fuel) ∧ PTreesSafe (gEAdd fuel) ∧
      PTreesSafe (gEMul fuel) ∧ PTreesSafe (gENot fuel) ∧
      PTreesSafe (gEField fuel) ∧ PTreesSafe (gEBase fuel) ∧
      PTreesSafe (gRawStruct fuel) ∧ PTreesSafe (gNmdStruct fuel) ∧
      PTreesSafe (gNmdFieldList fuel) ∧ PTreesSafe (gNmdField fuel) ∧
      PTreesSafe (gArgList fuel) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
        simp only [gExp, gEBoolAnd, gEEq, gECmp, gELoad, gELoadByte, gELoad32, gEOr,
          gEXor, gEAnd, gEShift, gEAdd, gEMul, gENot, gEField, gEBase, gRawStruct,
          gNmdStruct, gNmdFieldList, gNmdField, gArgList] <;>
        exact PTreesSafe.fail fuelExhausted
    | succ m =>
      obtain ⟨hExp, hBAnd, hEEq, hECmp, hELoad, hELoadByte, hELoad32, hEOr, hEXor,
        hEAnd, hEShift, hEAdd, hEMul, hENot, hEField, hEBase, hRaw, hNmd, hNmdList,
        hNmdField, hArgList⟩ := ih m (by omega)
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp only [gExp]
        exact subtree_rptBind_treesSafe .exp hBAnd (consume_treesSafe .boolOrT "||") hBAnd
      · simp only [gEBoolAnd]
        exact subtree_rptBind_treesSafe .eBoolAnd hEEq (consume_treesSafe .boolAndT "&&") hEEq
      · simp only [gEEq]
        exact subtree_tryChain_treesSafe .eEq hECmp gEqOps_treesSafe
      · simp only [gECmp]
        exact subtree_tryChain_treesSafe .eCmp hELoad gCmpOps_treesSafe
      · simp only [gELoad]
        refine PTreesSafe.orElse' ?_ hELoadByte
        refine subtree_treesSafe .eLoad ?_
        refine PTreesSafe.bind (consumeKw_treesSafe .ldsK "lds") (fun _ _ => ?_)
        refine PTreesSafe.bind (gShape_treesSafe m) (fun shape hs => ?_)
        refine PTreesSafe.bind hELoadByte (fun address ha => ?_)
        exact PTreesSafe.pure (shape ++ address) (TreesByteRanged.append hs ha)
      · simp only [gELoadByte]
        refine PTreesSafe.orElse' ?_ hELoad32
        refine subtree_treesSafe .eLoadByte ?_
        exact PTreesSafe.bind (consumeKw_treesSafe .ld8K "ld8") (fun _ _ => hELoad32)
      · simp only [gELoad32]
        refine PTreesSafe.orElse' ?_ hEOr
        refine subtree_treesSafe .eLoad32 ?_
        exact PTreesSafe.bind (consumeKw_treesSafe .ld32K "ld32") (fun _ _ => hEOr)
      · simp only [gEOr]
        exact subtree_rptChain_treesSafe .eOr hEXor (keepExact_treesSafe .orT "|")
      · simp only [gEXor]
        exact subtree_rptChain_treesSafe .eXor hEAnd (keepExact_treesSafe .xorT "^")
      · simp only [gEAnd]
        exact subtree_rptChain_treesSafe .eAnd hEShift (keepExact_treesSafe .andT "&")
      · simp only [gEShift]
        exact subtree_rptChain_treesSafe .eShift hEAdd gShiftOps_treesSafe
      · simp only [gEAdd]
        exact subtree_rptChain_treesSafe .eAdd hEMul gAddOps_treesSafe
      · simp only [gEMul]
        exact subtree_rptChain_treesSafe .eMul hENot gMulOps_treesSafe
      · simp only [gENot]
        refine subtree_treesSafe .eNot ?_
        refine PTreesSafe.bind (tryRule_treesSafe (keepExact_treesSafe .notT "!")) (fun negated hn => ?_)
        refine PTreesSafe.bind hEField (fun operand ho => ?_)
        exact PTreesSafe.pure (negated ++ operand) (TreesByteRanged.append hn ho)
      · simp only [gEField]
        exact subtree_rptBind_treesSafe .eField hEBase (consume_treesSafe .dotT ".") (PTreesSafe.orElse' keepNat_treesSafe keepIdent_treesSafe)
      · simp only [gEBase]
        refine PTreesSafe.orElse' ?_ ?_
        · refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
          refine PTreesSafe.bind hExp (fun inner hi => ?_)
          refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
          exact PTreesSafe.pure inner hi
        · refine PTreesSafe.orElse' (keepKw_treesSafe .trueK "true") ?_
          refine PTreesSafe.orElse' (keepKw_treesSafe .falseK "false") ?_
          refine PTreesSafe.orElse' hRaw ?_
          refine PTreesSafe.orElse' hNmd ?_
          refine PTreesSafe.orElse' (keepKw_treesSafe .baseK "@base") ?_
          refine PTreesSafe.orElse' (keepKw_treesSafe .biwK "@biw") ?_
          refine PTreesSafe.orElse' (keepKw_treesSafe .topK "@top") ?_
          exact PTreesSafe.orElse' keepInt_treesSafe keepIdent_treesSafe
      · simp only [gRawStruct]
        refine subtree_treesSafe .rawStruct ?_
        refine PTreesSafe.bind (consume_treesSafe .lessT "<") (fun _ _ => ?_)
        refine PTreesSafe.bind hArgList (fun fields hf => ?_)
        refine PTreesSafe.bind (consume_treesSafe .greaterT ">") (fun _ _ => ?_)
        exact PTreesSafe.pure fields hf
      · simp only [gNmdStruct]
        refine subtree_treesSafe .nmdStruct ?_
        refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lessT "<") (fun _ _ => ?_)
        refine PTreesSafe.bind hNmdList (fun fields hf => ?_)
        refine PTreesSafe.bind (consume_treesSafe .greaterT ">") (fun _ _ => ?_)
        exact PTreesSafe.pure (name ++ fields) (TreesByteRanged.append hn hf)
      · simp only [gNmdFieldList]
        exact subtree_rptBind_treesSafe .nmdFieldList hNmdField (consume_treesSafe .commaT ",") hNmdField
      · simp only [gNmdField]
        refine subtree_treesSafe .nmdField ?_
        refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
        refine PTreesSafe.bind (consume_treesSafe .assignT "=") (fun _ _ => ?_)
        refine PTreesSafe.bind hExp (fun value hv => ?_)
        exact PTreesSafe.pure (name ++ value) (TreesByteRanged.append hn hv)
      · simp only [gArgList]
        exact subtree_rptBind_treesSafe .argList hExp (consume_treesSafe .commaT ",") hExp


theorem gExp_treesSafe (fuel : Nat) : PTreesSafe (gExp fuel) :=
  (grammarBlock2_treesSafe fuel).1
theorem gEBoolAnd_treesSafe (fuel : Nat) : PTreesSafe (gEBoolAnd fuel) :=
  (grammarBlock2_treesSafe fuel).2.1
theorem gEEq_treesSafe (fuel : Nat) : PTreesSafe (gEEq fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.1
theorem gECmp_treesSafe (fuel : Nat) : PTreesSafe (gECmp fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.1
theorem gELoad_treesSafe (fuel : Nat) : PTreesSafe (gELoad fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.1
theorem gELoadByte_treesSafe (fuel : Nat) : PTreesSafe (gELoadByte fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.1
theorem gELoad32_treesSafe (fuel : Nat) : PTreesSafe (gELoad32 fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.1
theorem gEOr_treesSafe (fuel : Nat) : PTreesSafe (gEOr fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.1
theorem gEXor_treesSafe (fuel : Nat) : PTreesSafe (gEXor fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.1
theorem gEAnd_treesSafe (fuel : Nat) : PTreesSafe (gEAnd fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.1
theorem gEShift_treesSafe (fuel : Nat) : PTreesSafe (gEShift fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.1
theorem gEAdd_treesSafe (fuel : Nat) : PTreesSafe (gEAdd fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.1
theorem gEMul_treesSafe (fuel : Nat) : PTreesSafe (gEMul fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gENot_treesSafe (fuel : Nat) : PTreesSafe (gENot fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gEField_treesSafe (fuel : Nat) : PTreesSafe (gEField fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gEBase_treesSafe (fuel : Nat) : PTreesSafe (gEBase fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gRawStruct_treesSafe (fuel : Nat) : PTreesSafe (gRawStruct fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gNmdStruct_treesSafe (fuel : Nat) : PTreesSafe (gNmdStruct fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gNmdFieldList_treesSafe (fuel : Nat) : PTreesSafe (gNmdFieldList fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gNmdField_treesSafe (fuel : Nat) : PTreesSafe (gNmdField fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gArgList_treesSafe (fuel : Nat) : PTreesSafe (gArgList fuel) :=
  (grammarBlock2_treesSafe fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem tryDefault_treesSafe {p : P P.Trees} (hp : PTreesSafe p) (token : Token)
    (h : TokenNameByteRanged token) : PTreesSafe (P.tryDefault p token) := by
  unfold P.tryDefault
  exact PTreesSafe.orElse' hp (defaultLeaf_treesSafe token h)

theorem gStoreForm_treesSafe (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : PTreesSafe (gStoreForm nonterminal keyword described fuel) := by
  simp only [gStoreForm]
  refine subtree_treesSafe nonterminal ?_
  refine PTreesSafe.bind (consumeKw_treesSafe keyword described) (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun address ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun value hv => ?_)
  exact PTreesSafe.pure (address ++ value) (TreesByteRanged.append ha hv)

theorem gSharedLoad_treesSafe (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : PTreesSafe (gSharedLoad nonterminal keyword described fuel) := by
  simp only [gSharedLoad]
  refine subtree_treesSafe nonterminal ?_
  refine PTreesSafe.bind (consume_treesSafe .notT "!") (fun _ _ => ?_)
  refine PTreesSafe.bind (consumeKw_treesSafe keyword described) (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun address ha => ?_)
  exact PTreesSafe.pure (name ++ address) (TreesByteRanged.append hn ha)

theorem gSharedStore_treesSafe (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : PTreesSafe (gSharedStore nonterminal keyword described fuel) := by
  simp only [gSharedStore]
  refine subtree_treesSafe nonterminal ?_
  refine PTreesSafe.bind (consume_treesSafe .notT "!") (fun _ _ => ?_)
  refine PTreesSafe.bind (consumeKw_treesSafe keyword described) (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun address ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun value hv => ?_)
  exact PTreesSafe.pure (address ++ value) (TreesByteRanged.append ha hv)

theorem gAssign_treesSafe (fuel : Nat) : PTreesSafe (gAssign fuel) := by
  simp only [gAssign]
  refine subtree_treesSafe .assign ?_
  refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .assignT "=") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun value hv => ?_)
  exact PTreesSafe.pure (name ++ value) (TreesByteRanged.append hn hv)

theorem gExtCall_treesSafe (fuel : Nat) : PTreesSafe (gExtCall fuel) := by
  simp only [gExtCall]
  refine subtree_treesSafe .extCall ?_
  refine PTreesSafe.bind keepFfiIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun configuration hc => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun configurationLength hcl => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun array ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .commaT ",") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun arrayLength hal => ?_)
  refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
  exact PTreesSafe.pure (name ++ configuration ++ configurationLength ++ array ++ arrayLength)
    (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append
      (TreesByteRanged.append hn hc) hcl) ha) hal)

theorem gThrow_treesSafe (fuel : Nat) : PTreesSafe (gThrow fuel) := by
  simp only [gThrow]
  refine subtree_treesSafe .throwNT ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .throwK "throw") (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun exception he => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun value hv => ?_)
  exact PTreesSafe.pure (exception ++ value) (TreesByteRanged.append he hv)

theorem gReturn_treesSafe (fuel : Nat) : PTreesSafe (gReturn fuel) := by
  simp only [gReturn]
  refine subtree_treesSafe .returnNT ?_
  exact PTreesSafe.bind (consumeKw_treesSafe .retK "return") (fun _ _ => gExp_treesSafe fuel)

theorem gRetCall_treesSafe (fuel : Nat) : PTreesSafe (gRetCall fuel) := by
  simp only [gRetCall]
  refine subtree_treesSafe .retCall ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .retK "return") (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
  refine PTreesSafe.bind (tryRule_treesSafe (gArgList_treesSafe fuel)) (fun args ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
  exact PTreesSafe.pure (name ++ args) (TreesByteRanged.append hn ha)

theorem gCall_treesSafe (fuel : Nat) : PTreesSafe (gCall fuel) := by
  simp only [gCall]
  refine subtree_treesSafe .call ?_
  refine PTreesSafe.bind (tryDefault_treesSafe
    (PTreesSafe.orElse' (keepKw_treesSafe .retK "return") gRet_treesSafe) .notT
    (by simp [TokenNameByteRanged])) (fun ret hr => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
  refine PTreesSafe.bind (tryDefault_treesSafe (gArgList_treesSafe fuel) .notT
    (by simp [TokenNameByteRanged])) (fun args ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
  exact PTreesSafe.pure (ret ++ name ++ args) (TreesByteRanged.append (TreesByteRanged.append hr hn) ha)

theorem gExnDec_treesSafe (fuel : Nat) : PTreesSafe (gExnDec fuel) := by
  simp only [gExnDec]
  refine subtree_treesSafe .exnDec ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .exceptionK "exception") (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun exception he => ?_)
  refine PTreesSafe.bind (consume_treesSafe .colonT ":") (fun _ _ => ?_)
  refine PTreesSafe.bind (gShape_treesSafe fuel) (fun shape hs => ?_)
  refine PTreesSafe.bind (consume_treesSafe .semiT ";") (fun _ _ => ?_)
  exact PTreesSafe.pure (exception ++ shape) (TreesByteRanged.append he hs)

theorem gStructName_treesSafe (fuel : Nat) : PTreesSafe (gStructName fuel) := by
  simp only [gStructName]
  refine subtree_treesSafe .structName ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .namedK "struct") (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun name hn => ?_)
  refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => ?_)
  refine PTreesSafe.bind (gShapedIdentList_treesSafe .fieldNameList fuel) (fun fields hf => ?_)
  refine PTreesSafe.bind (consume_treesSafe .rCurT "}") (fun _ _ => ?_)
  exact PTreesSafe.pure (name ++ fields) (TreesByteRanged.append hn hf)

theorem gDecForm_treesSafe (nonterminal : Nonterminal) (fuel : Nat) :
    PTreesSafe (gDecForm nonterminal fuel) := by
  simp only [gDecForm]
  refine subtree_treesSafe nonterminal ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .varK "var") (fun _ _ => ?_)
  refine PTreesSafe.bind (gShapedIdent_treesSafe fuel) (fun shapedName hs => ?_)
  refine PTreesSafe.bind (consume_treesSafe .assignT "=") (fun _ _ => ?_)
  refine PTreesSafe.bind (gExp_treesSafe fuel) (fun value hv => ?_)
  refine PTreesSafe.bind (consume_treesSafe .semiT ";") (fun _ _ => ?_)
  exact PTreesSafe.pure (shapedName ++ value) (TreesByteRanged.append hs hv)

theorem gDecCallHead_treesSafe (fuel : Nat) : PTreesSafe (gDecCallHead fuel) := by
  simp only [gDecCallHead]
  refine subtree_treesSafe .decCall ?_
  refine PTreesSafe.bind (consumeKw_treesSafe .varK "var") (fun _ _ => ?_)
  refine PTreesSafe.bind (gShapedIdent_treesSafe fuel) (fun shapedName hs => ?_)
  refine PTreesSafe.bind (consume_treesSafe .assignT "=") (fun _ _ => ?_)
  refine PTreesSafe.bind keepIdent_treesSafe (fun function hf => ?_)
  refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
  refine PTreesSafe.bind (tryRule_treesSafe (gArgList_treesSafe fuel)) (fun args ha => ?_)
  refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
  refine PTreesSafe.bind (consume_treesSafe .semiT ";") (fun _ _ => ?_)
  exact PTreesSafe.pure (shapedName ++ function ++ args)
    (TreesByteRanged.append (TreesByteRanged.append hs hf) ha)



theorem PTreesSafe.bind_of_stateSafe {α : Type} {p : P α} {f : α → P P.Trees}
    (hp : PStateToksSafe p) (hf : ∀ a, PTreesSafe (f a)) :
    PTreesSafe (P.bind' p f) := by
  constructor
  · intro s trees s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      have hp1 := hp.1 s a s'' heq h
      exact (hf a).1 s'' trees s' hs hp1
    · rename_i s'' heq
      exact absurd (congrArg Prod.fst hs) (by simp)
  · intro s s' hs h
    simp only [P.bind'] at hs
    split at hs
    · rename_i a s'' heq
      have hp1 := hp.1 s a s'' heq h
      exact (hf a).2 s'' s' hs hp1
    · rename_i s'' heq
      simp only [Prod.mk.injEq] at hs
      rw [← hs.2]
      exact hp.2 s s'' heq h

set_option maxHeartbeats 8000000 in
theorem grammarBlock3_treesSafe : ∀ m,
    PTreesSafe (gProg m) ∧ PTreesSafe (gTryProg m) ∧ PTreesSafe (gBlock m) ∧
    PTreesSafe (gHandle m) ∧ PTreesSafe (gIf m) ∧ PTreesSafe (gWhile m) ∧
    PTreesSafe (gStmt m) ∧ PTreesSafe (gFun m) ∧ PTreesSafe (gTopDecList m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
        simp only [gProg, gTryProg, gBlock, gHandle, gIf, gWhile, gStmt, gFun, gTopDecList] <;>
        exact PTreesSafe.fail fuelExhausted
    | succ m =>
      obtain ⟨hProg, hTryProg, hBlock, hHandle, hIf, hWhile, hStmt, hFun, hTopDecList⟩ := ih m (by omega)
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp only [gProg]
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .prog ?_
          refine PTreesSafe.bind hBlock (fun block hb => ?_)
          refine PTreesSafe.bind hProg (fun rest hr => ?_)
          exact PTreesSafe.pure (block ++ rest) (TreesByteRanged.append hb hr)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .decCall ?_
          refine PTreesSafe.bind (gDecCallHead_treesSafe m) (fun declaration hd => ?_)
          refine PTreesSafe.bind hTryProg (fun body hb => ?_)
          exact PTreesSafe.pure (declaration ++ body) (TreesByteRanged.append hd hb)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .dec ?_
          refine PTreesSafe.bind (gDecForm_treesSafe .dec m) (fun declaration hd => ?_)
          refine PTreesSafe.bind hTryProg (fun body hb => ?_)
          exact PTreesSafe.pure (declaration ++ body) (TreesByteRanged.append hd hb)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .prog ?_
          refine PTreesSafe.bind keepAnnot_treesSafe (fun annotation ha => ?_)
          refine PTreesSafe.bind hProg (fun rest hr => ?_)
          exact PTreesSafe.pure (annotation ++ rest) (TreesByteRanged.append ha hr)
        refine PTreesSafe.orElse' ?_ (consume_treesSafe .rCurT "}")
        refine subtree_treesSafe .prog ?_
        refine PTreesSafe.bind hStmt (fun statement hs => ?_)
        refine PTreesSafe.bind (consume_treesSafe .semiT ";") (fun _ _ => ?_)
        refine PTreesSafe.bind hProg (fun rest hr => ?_)
        exact PTreesSafe.pure (statement ++ rest) (TreesByteRanged.append hs hr)
      · simp only [gTryProg]
        refine PTreesSafe.orElse' ?_ hProg
        refine subtree_treesSafe .prog ?_
        exact PTreesSafe.bind (consume_treesSafe .rCurT "}")
          (fun _ _ => defaultLeaf_treesSafe (.keywordT .skipK) (by simp [TokenNameByteRanged]))
      · simp only [gBlock]
        refine PTreesSafe.orElse' hHandle ?_
        exact PTreesSafe.orElse' hIf hWhile
      · simp only [gHandle]
        refine subtree_treesSafe .handle ?_
        refine PTreesSafe.bind (consumeKw_treesSafe .tryK "try") (fun _ _ => ?_)
        refine PTreesSafe.bind (tryDefault_treesSafe gRet_treesSafe .notT (by simp [TokenNameByteRanged])) (fun ret hr => ?_)
        refine PTreesSafe.bind keepIdent_treesSafe (fun function hf => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
        refine PTreesSafe.bind (tryDefault_treesSafe (gArgList_treesSafe m) .notT (by simp [TokenNameByteRanged])) (fun args ha => ?_)
        refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
        refine PTreesSafe.bind (consumeKw_treesSafe .catchK "catch") (fun _ _ => ?_)
        refine PTreesSafe.bind keepIdent_treesSafe (fun exception he => ?_)
        refine PTreesSafe.bind (consume_treesSafe .arrowT "=>") (fun _ _ => ?_)
        refine PTreesSafe.bind keepIdent_treesSafe (fun bound hb => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => ?_)
        refine PTreesSafe.bind hTryProg (fun handler hh => ?_)
        exact PTreesSafe.pure (ret ++ function ++ args ++ exception ++ bound ++ handler)
          (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append hr hf) ha) he) hb) hh)
      · simp only [gIf]
        refine subtree_treesSafe .ifNT ?_
        refine PTreesSafe.bind (consumeKw_treesSafe .ifK "if") (fun _ _ => ?_)
        refine PTreesSafe.bind (gExp_treesSafe m) (fun condition hc => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => ?_)
        refine PTreesSafe.bind hTryProg (fun thenBranch ht => ?_)
        have helse : PTreesSafe (P.bind' (P.consumeKw .elseK "else") (fun _ => P.bind' (P.consume .lCurT "{") (fun _ => gTryProg m))) :=
          PTreesSafe.bind (consumeKw_treesSafe .elseK "else")
            (fun _ _ => PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => hTryProg))
        refine PTreesSafe.bind (tryDefault_treesSafe helse (.keywordT .skipK) (by simp [TokenNameByteRanged])) (fun elseBranch he => ?_)
        exact PTreesSafe.pure (condition ++ thenBranch ++ elseBranch)
          (TreesByteRanged.append (TreesByteRanged.append hc ht) he)
      · simp only [gWhile]
        refine subtree_treesSafe .whileNT ?_
        refine PTreesSafe.bind (consumeKw_treesSafe .whileK "while") (fun _ _ => ?_)
        refine PTreesSafe.bind (gExp_treesSafe m) (fun condition hc => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => ?_)
        refine PTreesSafe.bind hTryProg (fun body hb => ?_)
        exact PTreesSafe.pure (condition ++ body) (TreesByteRanged.append hc hb)
      · simp only [gStmt]
        refine PTreesSafe.orElse' (keepKw_treesSafe .skipK "skip") ?_
        refine PTreesSafe.orElse' (gCall_treesSafe m) ?_
        refine PTreesSafe.orElse' (gAssign_treesSafe m) ?_
        refine PTreesSafe.orElse' (gStoreForm_treesSafe .store .stK "st" m) ?_
        refine PTreesSafe.orElse' (gStoreForm_treesSafe .storeByte .st8K "st8" m) ?_
        refine PTreesSafe.orElse' (gStoreForm_treesSafe .store32 .st32K "st32" m) ?_
        refine PTreesSafe.orElse' (gSharedLoad_treesSafe .sharedLoadByte .ld8K "ld8" m) ?_
        refine PTreesSafe.orElse' (gSharedLoad_treesSafe .sharedLoad16 .ld16K "ld16" m) ?_
        refine PTreesSafe.orElse' (gSharedLoad_treesSafe .sharedLoad32 .ld32K "ld32" m) ?_
        refine PTreesSafe.orElse' (gSharedLoad_treesSafe .sharedLoad .ldwK "ldw" m) ?_
        refine PTreesSafe.orElse' (gSharedStore_treesSafe .sharedStoreByte .st8K "st8" m) ?_
        refine PTreesSafe.orElse' (gSharedStore_treesSafe .sharedStore16 .st16K "st16" m) ?_
        refine PTreesSafe.orElse' (gSharedStore_treesSafe .sharedStore32 .st32K "st32" m) ?_
        refine PTreesSafe.orElse' (gSharedStore_treesSafe .sharedStore .stwK "stw" m) ?_
        refine PTreesSafe.orElse' (keepKw_treesSafe .brK "break") ?_
        refine PTreesSafe.orElse' (keepKw_treesSafe .contK "continue") ?_
        refine PTreesSafe.orElse' (gExtCall_treesSafe m) ?_
        refine PTreesSafe.orElse' (gThrow_treesSafe m) ?_
        refine PTreesSafe.orElse' (gRetCall_treesSafe m) ?_
        refine PTreesSafe.orElse' (gReturn_treesSafe m) ?_
        refine PTreesSafe.orElse' (keepKw_treesSafe .ticK "tick") ?_
        exact PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => hTryProg)
      · simp only [gFun]
        refine subtree_treesSafe .funNT ?_
        refine PTreesSafe.bind (tryDefault_treesSafe (keepKw_treesSafe .inlineK "inline") .noinlineT (by simp [TokenNameByteRanged])) (fun inline hi => ?_)
        refine PTreesSafe.bind (tryDefault_treesSafe (keepKw_treesSafe .exportK "export") .staticT (by simp [TokenNameByteRanged])) (fun exported he => ?_)
        refine PTreesSafe.bind (consumeKw_treesSafe .funK "fun") (fun _ _ => ?_)
        refine PTreesSafe.bind (gShapedIdent_treesSafe m) (fun shapedName hs => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lParT "(") (fun _ _ => ?_)
        refine PTreesSafe.bind (PTreesSafe.orElse' (gShapedIdentList_treesSafe .paramList m) (emptyNode_treesSafe .paramList)) (fun params hp => ?_)
        refine PTreesSafe.bind (consume_treesSafe .rParT ")") (fun _ _ => ?_)
        refine PTreesSafe.bind (consume_treesSafe .lCurT "{") (fun _ _ => ?_)
        refine PTreesSafe.bind hTryProg (fun body hb => ?_)
        exact PTreesSafe.pure (inline ++ exported ++ shapedName ++ params ++ body)
          (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append (TreesByteRanged.append hi he) hs) hp) hb)
      · simp only [gTopDecList]
        refine PTreesSafe.orElse' ?_ ?_
        · exact PTreesSafe.bind_of_stateSafe PStateToksSafe.atEnd (fun b => by
            cases b with
            | true => exact subtree_treesSafe .topDecList (PTreesSafe.pure [] TreesByteRanged.nil)
            | false => exact PTreesSafe.fail "Expected end of input")
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .topDecList ?_
          refine PTreesSafe.bind (hFun) (fun item hi => ?_)
          refine PTreesSafe.bind hTopDecList (fun rest hr => ?_)
          exact PTreesSafe.pure (item ++ rest) (TreesByteRanged.append hi hr)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .topDecList ?_
          refine PTreesSafe.bind (gDecForm_treesSafe .globalDec m) (fun item hi => ?_)
          refine PTreesSafe.bind hTopDecList (fun rest hr => ?_)
          exact PTreesSafe.pure (item ++ rest) (TreesByteRanged.append hi hr)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .topDecList ?_
          refine PTreesSafe.bind (gExnDec_treesSafe m) (fun item hi => ?_)
          refine PTreesSafe.bind hTopDecList (fun rest hr => ?_)
          exact PTreesSafe.pure (item ++ rest) (TreesByteRanged.append hi hr)
        refine PTreesSafe.orElse' ?_ ?_
        · refine subtree_treesSafe .topDecList ?_
          refine PTreesSafe.bind (gStructName_treesSafe m) (fun item hi => ?_)
          refine PTreesSafe.bind hTopDecList (fun rest hr => ?_)
          exact PTreesSafe.pure (item ++ rest) (TreesByteRanged.append hi hr)
        refine subtree_treesSafe .topDecList ?_
        refine PTreesSafe.bind keepAnnot_treesSafe (fun annotation ha => ?_)
        refine PTreesSafe.bind hTopDecList (fun rest hr => ?_)
        exact PTreesSafe.pure (annotation ++ rest) (TreesByteRanged.append ha hr)

theorem gProg_treesSafe (m : Nat) : PTreesSafe (gProg m) :=
  (grammarBlock3_treesSafe m).1

theorem gTryProg_treesSafe (m : Nat) : PTreesSafe (gTryProg m) :=
  (grammarBlock3_treesSafe m).2.1

theorem gBlock_treesSafe (m : Nat) : PTreesSafe (gBlock m) :=
  (grammarBlock3_treesSafe m).2.2.1

theorem gHandle_treesSafe (m : Nat) : PTreesSafe (gHandle m) :=
  (grammarBlock3_treesSafe m).2.2.2.1

theorem gIf_treesSafe (m : Nat) : PTreesSafe (gIf m) :=
  (grammarBlock3_treesSafe m).2.2.2.2.1

theorem gWhile_treesSafe (m : Nat) : PTreesSafe (gWhile m) :=
  (grammarBlock3_treesSafe m).2.2.2.2.2.1

theorem gStmt_treesSafe (m : Nat) : PTreesSafe (gStmt m) :=
  (grammarBlock3_treesSafe m).2.2.2.2.2.2.1

theorem gFun_treesSafe (m : Nat) : PTreesSafe (gFun m) :=
  (grammarBlock3_treesSafe m).2.2.2.2.2.2.2.1

theorem gTopDecList_treesSafe (m : Nat) : PTreesSafe (gTopDecList m) :=
  (grammarBlock3_treesSafe m).2.2.2.2.2.2.2.2


end Flapjack.Parser
