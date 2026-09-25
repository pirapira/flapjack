import Flapjack.Parser.ByteRanged
import Flapjack.Parser.Conversion
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.PanLang.Exp

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

/-- `convStructName` maps a byte-ranged tree to a byte-ranged structure name and
    a byte-ranged field list. -/
theorem convStructName_byteRanged {fuel : Nat} {tree : ParseTree}
    (ht : ParseTreeByteRanged tree) :
    ∀ result, convStructName fuel tree = some result →
      StringByteRanged result.1 ∧
        ∀ p ∈ result.2, StringByteRanged p.1 ∧ ShapeByteRanged p.2 := by
  intro result h
  cases hargs : tree.argsNT .structName with
  | none => simp [convStructName, hargs] at h
  | some children =>
    cases children with
    | nil => simp [convStructName, hargs] at h
    | cons nameTree rest =>
      cases rest with
      | nil => simp [convStructName, hargs] at h
      | cons fieldsTree rest2 =>
        cases rest2 with
        | cons x xs => simp [convStructName, hargs] at h
        | nil =>
          simp only [convStructName, hargs] at h
          cases hn : convIdent nameTree with
          | none => simp [hn] at h
          | some name =>
            simp only [hn] at h
            cases hf : convFieldNameList fuel fieldsTree with
            | none => simp [hf] at h
            | some fields =>
              simp only [hf] at h
              cases h
              have ht2 := argsNT_byteRanged ht hargs
              exact ⟨convIdent_byteRanged (ht2 nameTree (by simp)) hn,
                convFieldNameList_byteRanged (ht2 fieldsTree (by simp)) fields hf⟩


/-- `conv_var` returns a byte-ranged expression from a byte-ranged tree. -/
theorem convVar_byteRanged {width : Nat} {tree : ParseTree}
    (ht : ParseTreeByteRanged tree) :
    ∀ e, convVar (α := BitVec width) tree = some e → ExpByteRanged e := by
  intro e h
  unfold convVar at h
  cases hi : convIdent tree with
  | none => simp [hi] at h
  | some name =>
      simp only [hi, Option.map_some, Option.some.injEq] at h
      subst h
      simpa [ExpByteRanged, StringByteRanged, CharsByteRanged] using
        convIdent_byteRanged ht hi

/-- `conv_const` always returns a byte-ranged expression (only the numeric
    payload varies, which carries no identifier). -/
theorem convConst_byteRanged {width : Nat} (ofInt : Int → BitVec width)
    {tree : ParseTree} :
    ∀ e, convConst ofInt tree = some e → ExpByteRanged e := by
  intro e h
  unfold convConst at h
  cases hc : convInt tree with
  | none => simp [hc] at h
  | some value =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst h
      simp [ExpByteRanged]

/-- `conv_accessors` preserves byte-rangedness of the accumulator, provided
    every accessor tree is byte-ranged. -/
theorem convAccessors_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (trees : List ParseTree) (htrees : ∀ t ∈ trees, ParseTreeByteRanged t)
    (acc : Flapjack.Exp (BitVec width)) (hacc : ExpByteRanged acc) :
    ∀ r, convAccessors ofInt fuel trees acc = some r → ExpByteRanged r := by
  induction trees generalizing acc with
  | nil =>
      intro r h
      simp [convAccessors] at h
      subst h
      exact hacc
  | cons tree trees ih =>
      intro r h
      simp only [convAccessors] at h
      cases hn : convNat tree with
      | some index =>
          simp only [hn] at h
          exact ih (fun t hmem => htrees t (by simp [hmem]))
            (.rField index acc) hacc r h
      | none =>
          simp only [hn] at h
          cases hi : convIdent tree with
          | none => simp [hi] at h
          | some name =>
              simp only [hi] at h
              exact ih (fun t hmem => htrees t (by simp [hmem]))
                (.nField name acc)
                ⟨convIdent_byteRanged (htrees tree (by simp)) hi, hacc⟩ r h


theorem convExpList_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) →
      ∀ es, convExpList ofInt fuel trees = some es → ∀ e ∈ es, ExpByteRanged e := by
  intro trees
  induction trees with
  | nil =>
      intro ht es h e he
      simp [convExpList.eq_1] at h
      subst h
      simp at he
  | cons tree trees ih =>
      intro ht es h e he
      cases hv : convExp ofInt fuel tree with
      | none => simp [convExpList.eq_2, hv] at h
      | some value =>
          have hval : ExpByteRanged value := hH fuel (by omega) tree (ht tree (by simp)) value hv
          cases hvs : convExpList ofInt fuel trees with
          | none => simp [convExpList.eq_2, hv, hvs] at h
          | some values =>
              simp [convExpList.eq_2, hv, hvs] at h
              rw [← h] at he
              rw [List.mem_cons] at he
              rcases he with hhead | htail
              · subst hhead
                exact hval
              · exact ih (fun t hmem => ht t (by simp [hmem])) values hvs e htail

theorem convField_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ tree, ParseTreeByteRanged tree → ∀ f, convField ofInt fuel tree = some f →
      StringByteRanged f.1 ∧ ExpByteRanged f.2 := by
  intro tree ht f h
  cases hfuel : fuel with
  | zero => simp [hfuel, convField.eq_1] at h
  | succ g =>
      simp only [hfuel, convField.eq_2] at h
      cases hargs : tree.argsNT .nmdField with
      | none => simp [hargs] at h
      | some children =>
          cases children with
          | nil => simp [hargs] at h
          | cons nameTree rest =>
              cases rest with
              | nil => simp [hargs] at h
              | cons valueTree rest2 =>
                  cases rest2 with
                  | cons extra tail => simp [hargs] at h
                  | nil =>
                      simp only [hargs] at h
                      have ht2 := argsNT_byteRanged ht hargs
                      cases hn : convIdent nameTree with
                      | none => simp [hn] at h
                      | some name =>
                          have hname : StringByteRanged name :=
                            convIdent_byteRanged (ht2 nameTree (by simp)) hn
                          cases hv : convExp ofInt g valueTree with
                          | none => simp [hn, hv] at h
                          | some value =>
                              simp [hn, hv] at h
                              subst h
                              exact ⟨hname, hH g (by omega) valueTree
                                (ht2 valueTree (by simp)) value hv⟩

theorem convFields_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ fs, convFields ofInt fuel trees = some fs →
      ∀ f ∈ fs, StringByteRanged f.1 ∧ ExpByteRanged f.2 := by
  intro trees
  induction trees with
  | nil =>
      intro ht fs h f hf
      simp [convFields.eq_1] at h
      subst h
      simp at hf
  | cons tree trees ih =>
      intro ht fs h f hf
      cases hfd : convField ofInt fuel tree with
      | none => simp [convFields.eq_2, hfd] at h
      | some field =>
          have hfield : StringByteRanged field.1 ∧ ExpByteRanged field.2 :=
            convField_byteRanged ofInt fuel hH tree (ht tree (by simp)) field hfd
          cases hfs : convFields ofInt fuel trees with
          | none => simp [convFields.eq_2, hfd, hfs] at h
          | some fields =>
              simp [convFields.eq_2, hfd, hfs] at h
              rw [← h] at hf
              rw [List.mem_cons] at hf
              rcases hf with hhead | htail
              · subst hhead
                exact hfield
              · exact ih (fun t hmem => ht t (by simp [hmem])) fields hfs f htail

theorem convArgList_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ tree, ParseTreeByteRanged tree → ∀ es, convArgList ofInt fuel tree = some es →
      ∀ e ∈ es, ExpByteRanged e := by
  intro tree ht es h e he
  cases hfuel : fuel with
  | zero => simp [hfuel, convArgList.eq_1] at h
  | succ g =>
      simp only [hfuel, convArgList.eq_2] at h
      by_cases hnt : tree.tokcheck .notT = true
      · rw [if_pos hnt] at h
        simp at h
        subst h
        simp at he
      · rw [if_neg hnt] at h
        cases hargs : tree.argsNT .argList with
        | none => simp [hargs] at h
        | some children =>
            cases children with
            | nil => simp [hargs] at h
            | cons first rest =>
                simp only [hargs] at h
                refine convExpList_byteRanged ofInt g
                  (fun g' hg' => hH g' (by omega)) (first :: rest)
                  (argsNT_byteRanged ht hargs) es h e he

theorem convFieldList_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ tree, ParseTreeByteRanged tree → ∀ fs, convFieldList ofInt fuel tree = some fs →
      ∀ f ∈ fs, StringByteRanged f.1 ∧ ExpByteRanged f.2 := by
  intro tree ht fs h f hf
  cases hfuel : fuel with
  | zero => simp [hfuel, convFieldList.eq_1] at h
  | succ g =>
      simp only [hfuel, convFieldList.eq_2] at h
      cases hargs : tree.argsNT .nmdFieldList with
      | none => simp [hargs] at h
      | some children =>
          cases children with
          | nil => simp [hargs] at h
          | cons first rest =>
              simp only [hargs] at h
              refine convFields_byteRanged ofInt g
                (fun g' hg' => hH g' (by omega)) (first :: rest)
                (argsNT_byteRanged ht hargs) fs h f hf

theorem convComparison_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ left opTree right, ParseTreeByteRanged left → ParseTreeByteRanged opTree →
      ParseTreeByteRanged right → ∀ e, convComparison ofInt fuel left opTree right = some e →
      ExpByteRanged e := by
  intro left opTree right hl ho hr e h
  unfold convComparison at h
  cases hlc : convExp ofInt fuel left with
  | none => simp [hlc] at h
  | some lv =>
      cases hc : convCmp opTree with
      | none => simp [hlc, hc] at h
      | some p =>
          obtain ⟨op, swapped⟩ := p
          cases hrc : convExp ofInt fuel right with
          | none => simp [hlc, hc, hrc] at h
          | some rv =>
              simp [hlc, hc, hrc] at h
              subst h
              have hlv := hH fuel (by omega) left hl lv hlc
              have hrv := hH fuel (by omega) right hr rv hrc
              by_cases hs : swapped = true
              · simp [hs, ExpByteRanged, hlv, hrv]
              · simp [hs, ExpByteRanged, hlv, hrv]


end Flapjack.Parser
