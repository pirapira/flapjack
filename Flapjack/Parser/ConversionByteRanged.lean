import Flapjack.Parser.ByteRanged
import Flapjack.Parser.Conversion
import Flapjack.Pancake.PanLang.Shape

/-!
Byte-rangedness of the concrete parse tree and of the first conversion step.

`Flapjack/Parser/ByteRanged.lean` proves the executed lexer only ever produces
token names whose characters are bytes (`< 256`). This module starts lifting
that invariant into the conversion phase: it defines `ParseTreeByteRanged`
(every leaf token is byte-ranged) and shows the identifier-reading conversion
helpers `convIdent` and `convFfiIdent` only return byte-ranged strings from such
a tree.

This is the first, primitive slice of bead `flapjack-pxn.18.3.5.8.7.1.1.1`; the
remaining lift is the recursive conversion family (`convParams`, `convShape`,
the `convExp`/`convProg` mutual block, `convTopDec`/`convTopDecList`) and the
grammar invariant that `parseTopDecs` produces byte-ranged trees.
-/

namespace Flapjack.Parser

/-- Every leaf token of the tree is name-byte-ranged. -/
def ParseTreeByteRanged : ParseTree → Prop
  | .lf token _ => TokenNameByteRanged token
  | .nd _ children _ => ∀ child ∈ children, ParseTreeByteRanged child

theorem parseTreeByteRanged_lf {token : Token} {locs : Locs}
    (h : TokenNameByteRanged token) : ParseTreeByteRanged (.lf token locs) := by
  simpa [ParseTreeByteRanged] using h

theorem parseTreeByteRanged_nd_apply {nonterminal : Nonterminal} {children : List ParseTree}
    {locs : Locs} {child : ParseTree} (h : ParseTreeByteRanged (.nd nonterminal children locs))
    (hmem : child ∈ children) : ParseTreeByteRanged child := by
  have h' : ∀ child ∈ children, ParseTreeByteRanged child := by
    simpa [ParseTreeByteRanged] using h
  exact h' child hmem

/-- A byte-ranged tree's `destTok` is name-byte-ranged. -/
theorem destTok_byteRanged {tree : ParseTree} {token : Token}
    (ht : ParseTreeByteRanged tree) (h : tree.destTok = some token) :
    TokenNameByteRanged token := by
  cases tree with
  | lf tok locs =>
      simp only [ParseTree.destTok, Option.some.injEq] at h
      subst h
      simpa [ParseTreeByteRanged] using ht
  | nd nonterminal children locs =>
      simp [ParseTree.destTok] at h

/-- `conv_ident` returns a byte-ranged string from a byte-ranged tree. -/
theorem convIdent_byteRanged {tree : ParseTree} {name : String}
    (ht : ParseTreeByteRanged tree) (h : convIdent tree = some name) :
    StringByteRanged name := by
  cases tree with
  | lf token locs =>
      simp only [convIdent, ParseTree.destTok] at h
      cases token <;> simp_all [ParseTreeByteRanged, TokenNameByteRanged]
  | nd nonterminal children locs =>
      simp [convIdent, ParseTree.destTok] at h

/-- `conv_ffi_ident` returns a byte-ranged string from a byte-ranged tree. -/
theorem convFfiIdent_byteRanged {tree : ParseTree} {name : String}
    (ht : ParseTreeByteRanged tree) (h : convFfiIdent tree = some name) :
    StringByteRanged name := by
  cases tree with
  | lf token locs =>
      simp only [convFfiIdent, ParseTree.destTok] at h
      cases token <;> simp_all [ParseTreeByteRanged, TokenNameByteRanged]
  | nd nonterminal children locs =>
      simp [convFfiIdent, ParseTree.destTok] at h

open Flapjack.Pancake.PanLang

theorem convDefaultShape_byteRanged {tree : ParseTree} {shape : Shape}
    (h : convDefaultShape tree = some shape) : ShapeByteRanged shape := by
  unfold convDefaultShape at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq] at h
    subst h
    simp [ShapeByteRanged]
  · simp at h

theorem argsNT_byteRanged {tree : ParseTree} {nt : Nonterminal} {children : List ParseTree}
    (ht : ParseTreeByteRanged tree) (h : tree.argsNT nt = some children) :
    ∀ c ∈ children, ParseTreeByteRanged c := by
  cases tree with
  | lf tok loc => simp [ParseTree.argsNT] at h
  | nd n ch loc =>
      simp only [ParseTree.argsNT] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        subst h
        simp only [ParseTreeByteRanged] at ht
        exact ht
      · simp at h

mutual
  theorem convShape_byteRanged : ∀ (fuel : Nat) (tree : ParseTree),
      ParseTreeByteRanged tree → ∀ shape, convShape fuel tree = some shape → ShapeByteRanged shape
    | 0, _, _, _, h => by simp [convShape] at h
    | fuel + 1, tree, ht, shape, h => by
        simp only [convShape] at h
        split at h
        · rename_i d hd
          simp only [Option.some.injEq] at h
          subst h
          exact convDefaultShape_byteRanged hd
        · split at h
          · rename_i v hv
            split at h
            · simp at h
            · split at h
              · simp only [Option.some.injEq] at h; subst h; simp [ShapeByteRanged]
              · simp only [Option.some.injEq] at h; subst h
                simp only [ShapeByteRanged]
                intro c hc
                simp only [List.mem_replicate] at hc
                obtain ⟨-, rfl⟩ := hc
                simp [ShapeByteRanged]
          · split at h
            · rename_i name hn
              simp only [Option.some.injEq] at h
              subst h
              simpa [ShapeByteRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged ht hn
            · split at h
              · rename_i children hc
                simp only [Option.map_eq_some_iff] at h
                obtain ⟨shapes, hs, rfl⟩ := h
                simp only [ShapeByteRanged]
                intro s hmem
                exact convShapeList_byteRanged fuel children
                  (argsNT_byteRanged ht hc) shapes hs s hmem
              · simp at h
  theorem convShapeList_byteRanged : ∀ (fuel : Nat) (trees : List ParseTree),
      (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ shapes,
      convShape.convShapeList fuel trees = some shapes → ∀ s ∈ shapes, ShapeByteRanged s
    | fuel, [], _, shapes, h => by
        unfold convShape.convShapeList at h
        simp only [Option.some.injEq] at h
        subst h
        intro s hs
        simp at hs
    | fuel, tree :: trees, ht, shapes, h => by
        cases htree : convShape fuel tree with
        | none => simp [convShape.convShapeList, htree] at h
        | some shape =>
            simp [convShape.convShapeList, htree] at h
            cases hrec : convShape.convShapeList fuel trees with
            | none => simp [hrec] at h
            | some shapes' =>
                simp only [hrec, Option.bind_some, Option.some.injEq] at h
                rw [← h]
                intro s hs
                rw [List.mem_cons] at hs
                rcases hs with rfl | htail
                · exact convShape_byteRanged fuel tree (ht tree (by simp)) _ htree
                · exact convShapeList_byteRanged fuel trees (fun t hmem => ht t (by simp [hmem])) shapes' hrec s htail
end

theorem convParams_byteRanged : ∀ (fuel : Nat) (trees : List ParseTree),
    (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ params, convParams fuel trees = some params →
    ∀ p ∈ params, StringByteRanged p.1 ∧ ShapeByteRanged p.2 := by
  intro fuel trees
  fun_induction convParams fuel trees
  · intro ht params h p hp
    cases h
    simp at hp
  · rename_i shapeTree nameTree rest ih
    intro ht params h p hp
    cases hs : convShape fuel shapeTree with
    | none => simp [hs] at h
    | some shape =>
      simp only [hs] at h
      cases hn : convIdent nameTree with
      | none => simp [hn] at h
      | some name =>
        simp only [hn] at h
        cases hp2 : convParams fuel rest with
        | none => simp [hp2] at h
        | some restParams =>
          simp only [hp2] at h
          cases h
          rw [List.mem_cons] at hp
          rcases hp with rfl | htail
          · exact ⟨convIdent_byteRanged (ht nameTree (by simp)) hn,
              convShape_byteRanged fuel shapeTree (ht shapeTree (by simp)) _ hs⟩
          · exact ih (fun t hmem => ht t (by simp [hmem])) restParams hp2 p htail
  · intro ht params h p hp
    simp at h

/-- `convFieldNameList` maps a byte-ranged tree to byte-ranged field names and
    shapes, via `convParams`. -/
theorem convFieldNameList_byteRanged {fuel : Nat} {tree : ParseTree}
    (ht : ParseTreeByteRanged tree) :
    ∀ fields, convFieldNameList fuel tree = some fields →
      ∀ p ∈ fields, StringByteRanged p.1 ∧ ShapeByteRanged p.2 := by
  intro fields h p hp
  cases hargs : tree.argsNT .fieldNameList with
  | none => simp [convFieldNameList, hargs] at h
  | some children =>
      simp only [convFieldNameList, hargs] at h
      exact convParams_byteRanged fuel children (argsNT_byteRanged ht hargs) fields h p hp

end Flapjack.Parser
