import Flapjack.Parser.ByteRanged
import Flapjack.Parser.Conversion
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.PanLang.Exp
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanLang.Decl

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

theorem expByteRanged_op_pair {width : Nat} {op : BinOp} {a b : Exp (BitVec width)}
    (ha : ExpByteRanged a) (hb : ExpByteRanged b) : ExpByteRanged (.op op [a, b]) := by
  simp [ExpByteRanged, ListExpByteRanged, ha, hb]

theorem ListExpByteRanged_append {width : Nat} {l1 l2 : List (Exp (BitVec width))}
    (h1 : ListExpByteRanged l1) (h2 : ListExpByteRanged l2) : ListExpByteRanged (l1 ++ l2) := by
  induction l1 with
  | nil => simpa [ListExpByteRanged] using h2
  | cons e es ih =>
      simp only [ListExpByteRanged] at h1 ⊢
      exact ⟨h1.1, ih h1.2⟩

theorem convPanops_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convPanops ofInt fuel trees acc = some e → ExpByteRanged e := by
  have H : ∀ n, ∀ trees, trees.length = n →
      (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convPanops ofInt fuel trees acc = some e → ExpByteRanged e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro trees hlen ht acc hacc e h
    cases trees with
    | nil => simp [convPanops.eq_1] at h; subst h; exact hacc
    | cons opTree t =>
      cases t with
      | nil => simp [convPanops.eq_3] at h
      | cons operandTree rest =>
        have hlt : rest.length < n := by simp only [List.length_cons] at hlen; omega
        have hr : ∀ t ∈ rest, ParseTreeByteRanged t := fun t hmem => ht t (by simp [hmem])
        simp only [convPanops.eq_2] at h
        cases hop : convPanop opTree with
        | none => simp [hop] at h
        | some op' =>
          cases hoperand : convExp ofInt fuel operandTree with
          | none => simp [hop, hoperand] at h
          | some operand' =>
            simp [hop, hoperand] at h
            have hopnd := hH fuel (by omega) operandTree (ht operandTree (by simp)) operand' hoperand
            exact ih rest.length hlt rest rfl hr
              (.panOp op' [acc, operand'])
              (by simp [ExpByteRanged, ListExpByteRanged, hacc, hopnd]) e h
  intro trees
  exact H trees.length trees rfl

theorem convShifts_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convShifts ofInt fuel trees acc = some e → ExpByteRanged e := by
  have H : ∀ n, ∀ trees, trees.length = n →
      (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convShifts ofInt fuel trees acc = some e → ExpByteRanged e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro trees hlen ht acc hacc e h
    cases trees with
    | nil => simp [convShifts.eq_1] at h; subst h; exact hacc
    | cons opTree t =>
      cases t with
      | nil => simp [convShifts.eq_3] at h
      | cons operandTree rest =>
        have hlt : rest.length < n := by simp only [List.length_cons] at hlen; omega
        have hr : ∀ t ∈ rest, ParseTreeByteRanged t := fun t hmem => ht t (by simp [hmem])
        simp only [convShifts.eq_2] at h
        cases hop : convShift opTree with
        | none => simp [hop] at h
        | some op' =>
          cases hoperand : convExp ofInt fuel operandTree with
          | none => simp [hop, hoperand] at h
          | some operand' =>
            simp [hop, hoperand] at h
            have hopnd := hH fuel (by omega) operandTree (ht operandTree (by simp)) operand' hoperand
            exact ih rest.length hlt rest rfl hr
              (.shift op' acc operand')
              (by simp [ExpByteRanged, hacc, hopnd]) e h
  intro trees
  exact H trees.length trees rfl

theorem convBinaryExps_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convBinaryExps ofInt fuel trees acc = some e → ExpByteRanged e := by
  have H : ∀ n, ∀ trees, trees.length = n →
      (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ acc, ExpByteRanged acc →
      ∀ e, convBinaryExps ofInt fuel trees acc = some e → ExpByteRanged e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro trees hlen ht acc hacc e h
    cases trees with
    | nil => simp [convBinaryExps.eq_1] at h; subst h; exact hacc
    | cons opTree t =>
      cases t with
      | nil => simp [convBinaryExps.eq_3] at h
      | cons operandTree rest =>
        have hlt : rest.length < n := by simp only [List.length_cons] at hlen; omega
        have hr : ∀ t ∈ rest, ParseTreeByteRanged t := fun t hmem => ht t (by simp [hmem])
        simp only [convBinaryExps.eq_2] at h
        cases hop : convBinop opTree with
        | none => simp [hop] at h
        | some op' =>
          cases hoperand : convExp ofInt fuel operandTree with
          | none => simp [hop, hoperand] at h
          | some operand' =>
            simp [hop, hoperand] at h
            have hopnd := hH fuel (by omega) operandTree (ht operandTree (by simp)) operand' hoperand
            cases acc with
            | op bop args =>
              by_cases hc : ¬bop = op' ∨ isSubOp (.op bop args) = true
              · simp only [if_pos hc] at h
                exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.op bop args, operand'])
                  (expByteRanged_op_pair hacc hopnd) e h
              · simp only [if_neg hc] at h
                have hargs : ListExpByteRanged args := by simpa [ExpByteRanged] using hacc
                exact ih rest.length hlt rest rfl hr (Exp.op bop (args ++ [operand']))
                  (by
                    simp only [ExpByteRanged]
                    exact ListExpByteRanged_append hargs (by simp [ListExpByteRanged, hopnd]))
                  e h
            | const v => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.const v, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | var kind name => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.var kind name, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | rStruct fields => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.rStruct fields, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | rField index value => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.rField index value, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | nStruct name fields => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.nStruct name fields, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | nField name value => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.nField name value, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | load shape address => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.load shape address, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | load32 address => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.load32 address, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | loadByte address => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.loadByte address, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | panOp op args => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.panOp op args, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | cmp op l r => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.cmp op l r, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | shift op l r => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.shift op l r, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | baseAddr => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.baseAddr, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | topAddr => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.topAddr, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
            | bytesInWord => exact ih rest.length hlt rest rfl hr (Exp.op op' [Exp.bytesInWord, operand']) (expByteRanged_op_pair hacc hopnd) e (by simpa using h)
  intro trees
  exact H trees.length trees rfl

theorem listExpByteRanged_iff {width : Nat} (l : List (Exp (BitVec width))) :
    ListExpByteRanged l ↔ ∀ e ∈ l, ExpByteRanged e := by
  induction l with
  | nil => simp [ListExpByteRanged]
  | cons e es ih =>
      constructor
      · intro h x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact h.1
        · exact (ih.mp h.2) x hx
      · intro h
        exact ⟨h e (by simp), ih.mpr (fun x hx => h x (by simp [hx]))⟩

theorem listFieldByteRanged_iff {width : Nat} (l : List (String × Exp (BitVec width))) :
    ListFieldByteRanged l ↔
      ∀ p ∈ l, (∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2 := by
  induction l with
  | nil => simp [ListFieldByteRanged]
  | cons p ps ih =>
      constructor
      · intro h x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨h.1, h.2.1⟩
        · exact (ih.mp h.2.2) x hx
      · intro h
        have hp := h p (by simp)
        exact ⟨hp.1, hp.2, ih.mpr (fun x hx => h x (by simp [hx]))⟩

set_option maxHeartbeats 8000000 in
theorem convExp_byteRanged {width : Nat} (ofInt : Int → BitVec width) :
    ∀ fuel (tree : ParseTree), ParseTreeByteRanged tree → ∀ e, convExp ofInt fuel tree = some e → ExpByteRanged e := by
  have H : ∀ fuel, ∀ (tree : ParseTree), ParseTreeByteRanged tree → ∀ e, convExp ofInt fuel tree = some e → ExpByteRanged e := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind n ih =>
      intro tree ht e h
      cases n with
      | zero => rw [convExp.eq_1] at h; simp at h
      | succ m =>
        have hH : ∀ g, g ≤ m → ∀ t, ParseTreeByteRanged t → ∀ e, convExp ofInt g t = some e → ExpByteRanged e :=
          fun g hg => ih g (by omega)
        cases tree with
        | lf token locs =>
          rw [convExp.eq_def] at h
          split at h
          · simp at h
          · simp_all
          · by_cases hb : (ParseTree.lf token locs).tokcheck (Token.keywordT Keyword.baseK) = true
            · simp only [hb, if_true] at h; injection h with h; subst h; simp [ExpByteRanged]
            · simp only [hb] at h
              by_cases hto : (ParseTree.lf token locs).tokcheck (Token.keywordT Keyword.topK) = true
              · simp only [hto, if_true] at h; injection h with h; subst h; simp [ExpByteRanged]
              · simp only [hto] at h
                by_cases hbi : (ParseTree.lf token locs).tokcheck (Token.keywordT Keyword.biwK) = true
                · simp only [hbi, if_true] at h; injection h with h; subst h; simp [ExpByteRanged]
                · simp only [hbi] at h
                  by_cases htr : (ParseTree.lf token locs).tokcheck (Token.keywordT Keyword.trueK) = true
                  · simp only [htr, if_true] at h; injection h with h; subst h; simp [ExpByteRanged]
                  · simp only [htr] at h
                    by_cases hfa : (ParseTree.lf token locs).tokcheck (Token.keywordT Keyword.falseK) = true
                    · simp only [hfa, if_true] at h; injection h with h; subst h; simp [ExpByteRanged]
                    · simp only [hfa] at h
                      cases hc : convConst ofInt (ParseTree.lf token locs) with
                      | none =>
                        simp only [hc] at h
                        exact convVar_byteRanged ht e h
                      | some value =>
                        simp only [hc] at h
                        injection h with h; subst h
                        exact convConst_byteRanged ofInt value hc
        | nd nt children locs =>
          have ht' : ∀ c ∈ children, ParseTreeByteRanged c := by
            simpa [ParseTreeByteRanged] using ht
          cases nt
          case ind.succ.nd.rawStruct =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons args rest =>
              cases rest with
              | cons _ _ => rw [convExp.eq_def] at h; simp at h
              | nil =>
                rw [convExp.eq_def] at h
                cases hc : convArgList ofInt m args with
                | none => simp [hc] at h
                | some values =>
                  simp [hc] at h
                  subst h
                  exact (listExpByteRanged_iff values).mpr
                    (convArgList_byteRanged ofInt m hH args (ht' args (by simp)) values hc)
          case ind.succ.nd.nmdStruct =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons nameTree rest =>
              cases rest with
              | nil => rw [convExp.eq_def] at h; simp at h
              | cons fieldsTree rest2 =>
                cases rest2 with
                | cons _ _ => rw [convExp.eq_def] at h; simp at h
                | nil =>
                  rw [convExp.eq_def] at h
                  cases hn : convIdent nameTree with
                  | none => simp [hn] at h
                  | some name =>
                    cases hf : convFieldList ofInt m fieldsTree with
                    | none => simp [hn, hf] at h
                    | some fields =>
                      simp [hn, hf] at h
                      subst h
                      refine ⟨convIdent_byteRanged (ht' nameTree (by simp)) hn, ?_⟩
                      exact (listFieldByteRanged_iff fields).mpr
                        (convFieldList_byteRanged ofInt m hH fieldsTree (ht' fieldsTree (by simp)) fields hf)
          case ind.succ.nd.eField =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons base accessors =>
              rw [convExp.eq_def] at h
              cases hb : convExp ofInt m base with
              | none => simp [hb] at h
              | some value =>
                simp only [hb] at h
                exact convAccessors_byteRanged ofInt m accessors
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) base (ht' base (by simp)) value hb) e h
          case ind.succ.nd.eNot =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons operand rest =>
              cases rest with
              | cons head rest2 =>
                cases rest2 with
                | cons _ _ => rw [convExp.eq_def] at h; simp at h
                | nil =>
                  rw [convExp.eq_def] at h
                  cases hv : convExp ofInt m head with
                  | none => simp [hv] at h
                  | some value =>
                    simp [hv] at h
                    subst h
                    have hval := ih m (by omega) head (ht' head (by simp)) value hv
                    simpa [ExpByteRanged] using hval
              | nil =>
                rw [convExp.eq_def] at h
                exact ih m (by omega) operand (ht' operand (by simp)) e h
          case ind.succ.nd.eLoadByte =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons address rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                cases hv : convExp ofInt m address with
                | none => simp [hv] at h
                | some value =>
                  simp [hv] at h
                  subst h
                  simpa [ExpByteRanged] using ih m (by omega) address (ht' address (by simp)) value hv
              | cons _ _ => rw [convExp.eq_def] at h; simp at h
          case ind.succ.nd.eLoad32 =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons address rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                cases hv : convExp ofInt m address with
                | none => simp [hv] at h
                | some value =>
                  simp only [hv, Option.map_some, Option.some.injEq] at h
                  subst h
                  simpa [ExpByteRanged] using ih m (by omega) address (ht' address (by simp)) value hv
              | cons _ _ => rw [convExp.eq_def] at h; simp at h
          case ind.succ.nd.eLoad =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons shapeTree rest =>
              cases rest with
              | nil => rw [convExp.eq_def] at h; simp at h
              | cons address rest2 =>
                cases rest2 with
                | cons _ _ => rw [convExp.eq_def] at h; simp at h
                | nil =>
                  rw [convExp.eq_def] at h
                  cases hs : convShape m shapeTree with
                  | none => simp [hs] at h
                  | some shape =>
                    cases hv : convExp ofInt m address with
                    | none => simp [hs, hv] at h
                    | some value =>
                      simp [hs, hv] at h
                      subst h
                      exact ⟨convShape_byteRanged m shapeTree (ht' shapeTree (by simp)) shape hs,
                        ih m (by omega) address (ht' address (by simp)) value hv⟩
          case ind.succ.nd.eCmp =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons operand rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                exact ih m (by omega) operand (ht' operand (by simp)) e h
              | cons opTree rest2 =>
                cases rest2 with
                | cons right rest3 =>
                  cases rest3 with
                  | cons _ _ => rw [convExp.eq_def] at h; simp at h
                  | nil =>
                    rw [convExp.eq_def] at h
                    exact convComparison_byteRanged ofInt m hH operand opTree right
                      (ht' operand (by simp)) (ht' opTree (by simp)) (ht' right (by simp)) e h
                | nil => rw [convExp.eq_def] at h; simp at h
          case ind.succ.nd.eEq =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons operand rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                exact ih m (by omega) operand (ht' operand (by simp)) e h
              | cons opTree rest2 =>
                cases rest2 with
                | cons right rest3 =>
                  cases rest3 with
                  | cons _ _ => rw [convExp.eq_def] at h; simp at h
                  | nil =>
                    rw [convExp.eq_def] at h
                    exact convComparison_byteRanged ofInt m hH operand opTree right
                      (ht' operand (by simp)) (ht' opTree (by simp)) (ht' right (by simp)) e h
                | nil => rw [convExp.eq_def] at h; simp at h
          case ind.succ.nd.exp =>
            cases children with
            | nil =>
              rw [convExp.eq_def] at h
              simp [convExpList.eq_1] at h
              subst h
              simp [ExpByteRanged, ListExpByteRanged]
            | cons operand rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                exact ih m (by omega) operand (ht' operand (by simp)) e h
              | cons operand2 rest2 =>
                rw [convExp.eq_def] at h
                cases hv : convExpList ofInt m (operand :: operand2 :: rest2) with
                | none => simp [hv] at h
                | some values =>
                  simp [hv] at h
                  subst h
                  have hts : ∀ t ∈ (operand :: operand2 :: rest2), ParseTreeByteRanged t :=
                    fun t hmem => ht' t (by simp [hmem])
                  simpa [ExpByteRanged] using
                    (listExpByteRanged_iff values).mpr
                      (convExpList_byteRanged ofInt m hH (operand :: operand2 :: rest2) hts values hv)
          case ind.succ.nd.eBoolAnd =>
            cases children with
            | nil =>
              rw [convExp.eq_def] at h
              simp [convExpList.eq_1] at h
              subst h
              simp [ExpByteRanged, ListExpByteRanged]
            | cons operand rest =>
              cases rest with
              | nil =>
                rw [convExp.eq_def] at h
                exact ih m (by omega) operand (ht' operand (by simp)) e h
              | cons operand2 rest2 =>
                rw [convExp.eq_def] at h
                cases hv : convExpList ofInt m (operand :: operand2 :: rest2) with
                | none => simp [hv] at h
                | some values =>
                  simp [hv] at h
                  subst h
                  have hts : ∀ t ∈ (operand :: operand2 :: rest2), ParseTreeByteRanged t :=
                    fun t hmem => ht' t (by simp [hmem])
                  have hvals := convExpList_byteRanged ofInt m hH (operand :: operand2 :: rest2) hts values hv
                  simp only [ExpByteRanged]
                  exact (listExpByteRanged_iff _).mpr (by
                    intro x hx
                    simp only [List.mem_map] at hx
                    obtain ⟨v, hvmem, rfl⟩ := hx
                    exact ⟨trivial, hvals v hvmem⟩)
          case ind.succ.nd.eShift =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convShifts_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          case ind.succ.nd.eOr =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convBinaryExps_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          case ind.succ.nd.eXor =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convBinaryExps_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          case ind.succ.nd.eAnd =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convBinaryExps_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          case ind.succ.nd.eAdd =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convBinaryExps_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          case ind.succ.nd.eMul =>
            cases children with
            | nil => rw [convExp.eq_def] at h; simp at h
            | cons first rest =>
              rw [convExp.eq_def] at h
              cases hv : convExp ofInt m first with
              | none => simp [hv] at h
              | some value =>
                simp only [hv] at h
                exact convPanops_byteRanged ofInt m hH rest
                  (fun t hmem => ht' t (by simp [hmem])) value
                  (ih m (by omega) first (ht' first (by simp)) value hv) e h
          all_goals (rw [convExp.eq_def] at h; try (simp at h))
  exact H


theorem convDecForm_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (nt : Nonterminal) : ∀ (tree : ParseTree), ParseTreeByteRanged tree → ∀ r,
      convDecForm ofInt fuel nt tree = some r →
      ShapeByteRanged r.1 ∧ StringByteRanged r.2.1 ∧ ExpByteRanged r.2.2 := by
  intro tree ht r h
  unfold convDecForm at h
  cases hargs : tree.argsNT nt with
  | none => simp [hargs] at h
  | some children =>
    cases children with
    | nil => simp [hargs] at h
    | cons a rest =>
      cases rest with
      | nil => simp [hargs] at h
      | cons b rest2 =>
        cases rest2 with
        | nil => simp [hargs] at h
        | cons c rest3 =>
          cases rest3 with
          | cons d rest4 => simp [hargs] at h
          | nil =>
            simp only [hargs] at h
            cases hs : convShape fuel a with
            | none => simp [hs] at h
            | some shape =>
              simp only [hs] at h
              cases hn : convIdent b with
              | none => simp [hn] at h
              | some name =>
                simp only [hn] at h
                cases hv : convExp ofInt fuel c with
                | none => simp [hv] at h
                | some value =>
                  simp only [hv] at h
                  injection h with h; subst h
                  exact ⟨convShape_byteRanged fuel a (argsNT_byteRanged ht hargs a (by simp)) shape hs,
                         convIdent_byteRanged (argsNT_byteRanged ht hargs b (by simp)) hn,
                         convExp_byteRanged ofInt fuel c (argsNT_byteRanged ht hargs c (by simp)) value hv⟩

theorem convExnDec_byteRanged (fuel : Nat) : ∀ (tree : ParseTree), ParseTreeByteRanged tree →
    ∀ r, convExnDec fuel tree = some r → StringByteRanged r.1 ∧ ShapeByteRanged r.2 := by
  intro tree ht r h
  unfold convExnDec at h
  cases hargs : tree.argsNT .exnDec with
  | none => simp [hargs] at h
  | some children =>
    cases children with
    | nil => simp [hargs] at h
    | cons a rest =>
      cases rest with
      | nil => simp [hargs] at h
      | cons b rest2 =>
        cases rest2 with
        | cons c rest3 => simp [hargs] at h
        | nil =>
          simp only [hargs] at h
          cases he : convIdent a with
          | none => simp [he] at h
          | some name =>
            simp only [he] at h
            cases hs : convShape fuel b with
            | none => simp [hs] at h
            | some shape =>
              simp only [hs] at h
              injection h with h; subst h
              exact ⟨convIdent_byteRanged (argsNT_byteRanged ht hargs a (by simp)) he,
                     convShape_byteRanged fuel b (argsNT_byteRanged ht hargs b (by simp)) shape hs⟩

theorem convDecCall_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat) :
    ∀ (tree : ParseTree), ParseTreeByteRanged tree → ∀ r,
      convDecCall ofInt fuel tree = some r →
      ShapeByteRanged r.1 ∧ StringByteRanged r.2.1 ∧ StringByteRanged r.2.2.1 ∧
        ∀ e ∈ r.2.2.2, ExpByteRanged e := by
  intro tree ht r h
  unfold convDecCall at h
  cases hargs : tree.argsNT .decCall with
  | none => simp [hargs] at h
  | some children =>
    cases children with
    | nil => simp [hargs] at h
    | cons shapeTree rest =>
      cases rest with
      | nil => simp [hargs] at h
      | cons nameTree rest2 =>
        cases rest2 with
        | nil => simp [hargs] at h
        | cons functionTree rest3 =>
          simp only [hargs] at h
          cases hs : convShape fuel shapeTree with
          | none => simp [hs] at h
          | some shape =>
            simp only [hs] at h
            cases hn : convIdent nameTree with
            | none => simp [hn] at h
            | some name =>
              simp only [hn] at h
              cases hf : convIdent functionTree with
              | none => simp [hf] at h
              | some fn =>
                simp only [hf] at h
                cases rest3 with
                | nil =>
                  simp only at h
                  injection h with h; subst h
                  exact ⟨convShape_byteRanged fuel shapeTree (argsNT_byteRanged ht hargs shapeTree (by simp)) shape hs,
                         convIdent_byteRanged (argsNT_byteRanged ht hargs nameTree (by simp)) hn,
                         convIdent_byteRanged (argsNT_byteRanged ht hargs functionTree (by simp)) hf,
                         by intro e he; simp at he⟩
                | cons argsTree rest4 =>
                  simp only at h
                  cases ha : convArgList ofInt fuel argsTree with
                  | none => simp [ha] at h
                  | some args =>
                    simp only [ha] at h
                    injection h with h; subst h
                    exact ⟨convShape_byteRanged fuel shapeTree (argsNT_byteRanged ht hargs shapeTree (by simp)) shape hs,
                           convIdent_byteRanged (argsNT_byteRanged ht hargs nameTree (by simp)) hn,
                           convIdent_byteRanged (argsNT_byteRanged ht hargs functionTree (by simp)) hf,
                           convArgList_byteRanged ofInt fuel (fun g _ => convExp_byteRanged ofInt g)
                             argsTree (argsNT_byteRanged ht hargs argsTree (by simp)) args ha⟩

theorem convRet_byteRanged : ∀ (tree : ParseTree), ParseTreeByteRanged tree → ∀ r,
    convRet tree = some r → ∀ vk name, r = some (some (vk, name)) → StringByteRanged name := by
  intro tree ht r h vk name hr
  unfold convRet at h
  by_cases h1 : tree.tokcheck (.keywordT .retK) = true
  · rw [if_pos h1] at h
    injection h with h; subst h
    simp at hr
  · rw [if_neg h1] at h
    by_cases h2 : tree.tokcheck .notT = true
    · rw [if_pos h2] at h
      injection h with h; subst h
      simp at hr
    · rw [if_neg h2] at h
      cases hargs : tree.argsNT .ret with
      | none => simp [hargs] at h
      | some children =>
        cases children with
        | nil => simp [hargs] at h
        | cons a rest =>
          cases rest with
          | cons b rest2 => simp [hargs] at h
          | nil =>
            simp only [hargs] at h
            cases hn : convIdent a with
            | none => simp [hn] at h
            | some n =>
              simp only [hn] at h
              injection h with h; subst h
              simp only [Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨_, rfl⟩ := hr
              exact convIdent_byteRanged (argsNT_byteRanged ht hargs a (by simp)) hn


theorem convNonRecStmt_byteRanged {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat) :
    ∀ tree, ParseTreeByteRanged tree → ∀ p, convNonRecStmt ofInt fuel tree = some p →
      ProgByteRanged p := by
  intro tree ht p h
  cases tree with
  | lf token locs =>
    simp only [convNonRecStmt] at h
    by_cases h1 : (ParseTree.lf token locs).tokcheck (.keywordT .skipK) = true
    · rw [if_pos h1] at h; simp only [Option.some.injEq] at h; subst h; exact trivial
    · rw [if_neg h1] at h
      by_cases h2 : (ParseTree.lf token locs).tokcheck (.keywordT .brK) = true
      · rw [if_pos h2] at h; simp only [Option.some.injEq] at h; subst h; exact trivial
      · rw [if_neg h2] at h
        by_cases h3 : (ParseTree.lf token locs).tokcheck (.keywordT .contK) = true
        · rw [if_pos h3] at h; simp only [Option.some.injEq] at h; subst h; exact trivial
        · rw [if_neg h3] at h
          by_cases h4 : (ParseTree.lf token locs).tokcheck (.keywordT .ticK) = true
          · rw [if_pos h4] at h; simp only [Option.some.injEq] at h; subst h; exact trivial
          · rw [if_neg h4] at h
            cases token with
            | annotCommentT text =>
              simp [destAnnotTok, ParseTree.destTok] at h
              subst h
              exact ⟨by decide,
                by simpa [ParseTreeByteRanged, TokenNameByteRanged, NameRanged, StringByteRanged, CharsByteRanged] using ht⟩
            | _ => simp [destAnnotTok, ParseTree.destTok] at h
  | nd nonterminal children locs =>
    have ht' : ∀ c ∈ children, ParseTreeByteRanged c := by simpa [ParseTreeByteRanged] using ht
    cases nonterminal
    case nd.assign =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.store =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.storeByte =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.store32 =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedLoad =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedLoad] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedLoadByte =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedLoad] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedLoad16 =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedLoad] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedLoad32 =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedLoad] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedStore =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedStore] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedStoreByte =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedStore] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedStore16 =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedStore] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.sharedStore32 =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt, convNonRecStmt.convSharedStore] at h
            cases h0 : convExp ofInt fuel n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨convExp_byteRanged ofInt fuel n0 (ht' n0 (by simp)) _ h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.throwNT =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons n0 rest =>
        cases rest with
        | nil => simp [convNonRecStmt] at h
        | cons n1 rest =>
          cases rest with
          | nil =>
            simp only [convNonRecStmt] at h
            cases h0 : convIdent n0 with
            | none => simp [h0] at h
            | some v0 =>
              simp [h0] at h
              cases h1 : convExp ofInt fuel n1 with
              | none => simp [h1] at h
              | some v1 =>
                simp [h1] at h
                subst h
                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' n0 (by simp)) h0,
                       convExp_byteRanged ofInt fuel n1 (ht' n1 (by simp)) _ h1⟩
          | cons n2 rest => simp [convNonRecStmt] at h
    case nd.returnNT =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons valueTree rest =>
        cases rest with
        | nil =>
          simp only [convNonRecStmt] at h
          cases hv : convExp ofInt fuel valueTree with
          | none => simp [hv] at h
          | some value =>
            simp [hv] at h
            subst h
            exact convExp_byteRanged ofInt fuel valueTree (ht' valueTree (by simp)) _ hv
        | cons extra rest => simp [convNonRecStmt] at h
    case nd.extCall =>
      cases children with
      | nil => simp [convNonRecStmt] at h
      | cons nameTree rest0 =>
        cases rest0 with
        | nil => simp [convNonRecStmt] at h
        | cons configurationTree rest1 =>
          cases rest1 with
          | nil => simp [convNonRecStmt] at h
          | cons configurationLengthTree rest2 =>
            cases rest2 with
            | nil => simp [convNonRecStmt] at h
            | cons arrayTree rest3 =>
              cases rest3 with
              | nil => simp [convNonRecStmt] at h
              | cons arrayLengthTree rest4 =>
                cases rest4 with
                | nil =>
                  simp only [convNonRecStmt] at h
                  cases hf : convFfiIdent nameTree with
                  | none => simp [hf] at h
                  | some function =>
                    simp [hf] at h
                    cases hc : convExp ofInt fuel configurationTree with
                    | none => simp [hc] at h
                    | some configuration =>
                      simp [hc] at h
                      cases hl : convExp ofInt fuel configurationLengthTree with
                      | none => simp [hl] at h
                      | some configurationLength =>
                        simp [hl] at h
                        cases ha : convExp ofInt fuel arrayTree with
                        | none => simp [ha] at h
                        | some array =>
                          simp [ha] at h
                          cases hal : convExp ofInt fuel arrayLengthTree with
                          | none => simp [hal] at h
                          | some arrayLength =>
                            simp [hal] at h
                            subst h
                            simp only [ProgByteRanged]
                            exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convFfiIdent_byteRanged (ht' nameTree (by simp)) hf,
                              convExp_byteRanged ofInt fuel configurationTree (ht' configurationTree (by simp)) _ hc,
                              convExp_byteRanged ofInt fuel configurationLengthTree (ht' configurationLengthTree (by simp)) _ hl,
                              convExp_byteRanged ofInt fuel arrayTree (ht' arrayTree (by simp)) _ ha,
                              convExp_byteRanged ofInt fuel arrayLengthTree (ht' arrayLengthTree (by simp)) _ hal⟩
                | cons extra rest => simp [convNonRecStmt] at h
    all_goals (simp [convNonRecStmt] at h)


theorem charsByteRanged_append {l1 l2 : List Char} (h1 : CharsByteRanged l1) (h2 : CharsByteRanged l2) :
    CharsByteRanged (l1 ++ l2) := by
  intro c hc; rw [List.mem_append] at hc
  rcases hc with hc | hc
  · exact h1 c hc
  · exact h2 c hc

theorem stringByteRanged_append {s1 s2 : String} (h1 : StringByteRanged s1) (h2 : StringByteRanged s2) :
    StringByteRanged (s1 ++ s2) := by
  unfold StringByteRanged at *
  rw [String.toList_append]
  exact charsByteRanged_append h1 h2

theorem toString_eq_self (s : String) : toString s = s := rfl

theorem natToString_byteRanged (n : Nat) : StringByteRanged (toString n) := by
  rw [Nat.toString_eq_ofList_toDigits]
  unfold StringByteRanged CharsByteRanged
  intro c hc
  simp only [String.toList_ofList] at hc
  have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide) hc
  have hb := Char.isDigit_iff_toNat.mp hd
  have h57 : ('9' : Char).toNat = 57 := by decide
  omega

theorem posnString_byteRanged : ∀ p : Posn, StringByteRanged (posnString p)
  | .posn row col => by
      show StringByteRanged (toString row ++ ":" ++ toString col)
      exact stringByteRanged_append
        (stringByteRanged_append (natToString_byteRanged row)
          (by unfold StringByteRanged CharsByteRanged; decide))
        (natToString_byteRanged col)
  | .eofPt => by unfold posnString StringByteRanged CharsByteRanged; decide
  | .unknownPt => by unfold posnString StringByteRanged CharsByteRanged; decide

theorem locationTag_byteRanged : StringByteRanged locationTag := by
  unfold locationTag StringByteRanged CharsByteRanged; decide

theorem locsComment_byteRanged (locs : Locs) : StringByteRanged (locsComment locs) := by
  rcases locs with ⟨start, stop⟩
  show StringByteRanged (toString "(" ++ toString (posnString start) ++ toString " " ++ toString (posnString stop) ++ toString ")")
  rw [toString_eq_self (posnString start), toString_eq_self (posnString stop)]
  simp only [toString_eq_self]
  exact stringByteRanged_append
    (stringByteRanged_append
      (stringByteRanged_append
        (stringByteRanged_append (by unfold StringByteRanged CharsByteRanged; decide)
          (posnString_byteRanged start))
        (by unfold StringByteRanged CharsByteRanged; decide))
      (posnString_byteRanged stop))
    (by unfold StringByteRanged CharsByteRanged; decide)

theorem addLocsAnnot_byteRanged {width : Nat} (locations : Bool) (tree : ParseTree)
    {program : Flapjack.Prog (BitVec width)} (hp : ProgByteRanged program) :
    ProgByteRanged (addLocsAnnot locations tree program) := by
  unfold addLocsAnnot
  by_cases h : locations = true
  · simp only [h, if_true]
    show ProgByteRanged (Flapjack.Prog.seq (Flapjack.Prog.annot locationTag (locsComment tree.locs)) program)
    exact ⟨⟨locationTag_byteRanged, locsComment_byteRanged tree.locs⟩, hp⟩
  · simp only [h]
    exact hp

mutual
  theorem shapeVal_byteRanged {width : Nat} (ofInt : Int → BitVec width) :
      ∀ shape, ShapeByteRanged shape → ExpByteRanged (shapeVal ofInt shape)
    | .one, _ => by simp [shapeVal, ExpByteRanged]
    | .named _, _ => by simp [shapeVal, ExpByteRanged]
    | .comb shapes, hs => by
        have hs' : ∀ s ∈ shapes, ShapeByteRanged s := by simpa [ShapeByteRanged] using hs
        show ListExpByteRanged (shapeVal.shapeVals ofInt shapes)
        exact shapeVals_byteRanged ofInt shapes hs'
  theorem shapeVals_byteRanged {width : Nat} (ofInt : Int → BitVec width) :
      ∀ shapes, (∀ s ∈ shapes, ShapeByteRanged s) → ListExpByteRanged (shapeVal.shapeVals ofInt shapes)
    | [], _ => by simp [shapeVal.shapeVals, ListExpByteRanged]
    | s :: ss, h => by
        simp only [shapeVal.shapeVals, ListExpByteRanged]
        exact ⟨shapeVal_byteRanged ofInt s (h s (by simp)),
          shapeVals_byteRanged ofInt ss (fun x hx => h x (by simp [hx]))⟩
end

set_option maxHeartbeats 8000000 in
theorem convProg_convProgSeq_byteRanged {width : Nat} (ofInt : Int → BitVec width)
    (locations : Bool) :
    ∀ fuel,
      (∀ tree, ParseTreeByteRanged tree → ∀ p, convProg ofInt locations fuel tree = some p →
        ProgByteRanged p) ∧
      (∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ p,
        convProgSeq ofInt locations fuel trees = some p → ProgByteRanged p) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro tree ht p h
        rw [convProg.eq_1] at h
        simp at h
      · intro trees ht p h
        cases trees with
        | nil => rw [convProgSeq.eq_1] at h; simp at h
        | cons t ts =>
          cases ts with
          | nil =>
            rw [convProgSeq.eq_2] at h
            rw [convProg.eq_1] at h
            simp at h
          | cons u us =>
            rw [convProgSeq.eq_3] at h
            · cases hf : convProg ofInt locations 0 t with
              | none => simp_all
              | some first => rw [convProg.eq_1] at hf; simp at hf
            · simp
    | succ m =>
      have ihP : ∀ tree, ParseTreeByteRanged tree → ∀ p,
          convProg ofInt locations m tree = some p → ProgByteRanged p := (ih m (by omega)).1
      have ihS : ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ p,
          convProgSeq ofInt locations m trees = some p → ProgByteRanged p := (ih m (by omega)).2
      have hP : ∀ tree, ParseTreeByteRanged tree → ∀ p,
          convProg ofInt locations (m + 1) tree = some p → ProgByteRanged p := by
        intro tree ht p h
        cases tree with
        | lf token locs =>
          simp only [convProg] at h
          cases hc : convNonRecStmt ofInt m (ParseTree.lf token locs) with
          | none => simp_all
          | some q =>
            simp only [hc, Option.map_some, Option.some.injEq] at h
            subst h
            exact addLocsAnnot_byteRanged locations (ParseTree.lf token locs)
              (convNonRecStmt_byteRanged ofInt m (ParseTree.lf token locs) ht q hc)
        | nd nt children locs' =>
          have ht' : ∀ c ∈ children, ParseTreeByteRanged c := by
            simpa [ParseTreeByteRanged] using ht
          have hnonrec : ∀ tree, ParseTreeByteRanged tree → ∀ p,
              (convNonRecStmt ofInt m tree).map (addLocsAnnot locations tree) = some p →
                ProgByteRanged p := by
            intro tree ht p h
            cases hc : convNonRecStmt ofInt m tree with
            | none => simp_all
            | some q =>
              simp only [hc, Option.map_some, Option.some.injEq] at h
              subst h
              exact addLocsAnnot_byteRanged locations tree
                (convNonRecStmt_byteRanged ofInt m tree ht q hc)
          cases nt
          case nd.dec =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | cons c rest3 => simp only [convProg] at h; exact hnonrec _ ht p h
                | nil =>
                  simp only [convProg] at h
                  cases hd : convDecForm ofInt m .dec a with
                  | none => simp_all
                  | some r =>
                    obtain ⟨shape, name, value⟩ := r
                    cases hb : convProg ofInt locations m b with
                    | none => simp_all
                    | some body =>
                      simp [hd, hb] at h
                      subst h
                      obtain ⟨hshape, hname, hvalue⟩ := convDecForm_byteRanged ofInt m .dec a (ht' a (by simp)) _ hd
                      apply addLocsAnnot_byteRanged
                      exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using hname,
                        hshape, hvalue, ihP b (ht' b (by simp)) body hb⟩
          case nd.ifNT =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | nil => simp only [convProg] at h; exact hnonrec _ ht p h
                | cons c rest3 =>
                  cases rest3 with
                  | cons d rest4 => simp only [convProg] at h; exact hnonrec _ ht p h
                  | nil =>
                    simp only [convProg] at h
                    cases hc : convExp ofInt m a with
                    | none => simp_all
                    | some condition =>
                      cases hb : convProg ofInt locations m b with
                      | none => simp_all
                      | some thenBranch =>
                        cases hb2 : convProg ofInt locations m c with
                        | none => simp_all
                        | some elseBranch =>
                          simp [hc, hb, hb2] at h
                          subst h
                          apply addLocsAnnot_byteRanged
                          exact ⟨convExp_byteRanged ofInt m a (ht' a (by simp)) _ hc,
                            ihP b (ht' b (by simp)) thenBranch hb,
                            ihP c (ht' c (by simp)) elseBranch hb2⟩
          case nd.whileNT =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | cons c rest3 => simp only [convProg] at h; exact hnonrec _ ht p h
                | nil =>
                  simp only [convProg] at h
                  cases hc : convExp ofInt m a with
                  | none => simp_all
                  | some condition =>
                    cases hb : convProg ofInt locations m b with
                    | none => simp_all
                    | some body =>
                      simp [hc, hb] at h
                      subst h
                      apply addLocsAnnot_byteRanged
                      exact ⟨convExp_byteRanged ofInt m a (ht' a (by simp)) _ hc,
                        ihP b (ht' b (by simp)) body hb⟩
          case nd.decCall =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | cons c rest3 => simp only [convProg] at h; exact hnonrec _ ht p h
                | nil =>
                  simp only [convProg] at h
                  cases hd : convDecCall ofInt m a with
                  | none => simp_all
                  | some r =>
                    obtain ⟨shape, name, function, args⟩ := r
                    cases hb : convProg ofInt locations m b with
                    | none => simp_all
                    | some body =>
                      by_cases hf : function = addWithCarryName
                      · simp [hd, hb, hf] at h
                        subst h
                        obtain ⟨hshape, hname, hfn, hargs⟩ := convDecCall_byteRanged ofInt m a (ht' a (by simp)) _ hd
                        apply addLocsAnnot_byteRanged
                        refine ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using hname,
                          hshape, ?_, ?_⟩
                        · simpa [shapeValViaHOL_eq_shapeVal] using
                            shapeVal_byteRanged ofInt shape hshape
                        · exact ⟨⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using hname,
                            hargs⟩, ihP b (ht' b (by simp)) body hb⟩
                      · simp [hd, hb, hf] at h
                        subst h
                        obtain ⟨hshape, hname, hfn, hargs⟩ := convDecCall_byteRanged ofInt m a (ht' a (by simp)) _ hd
                        apply addLocsAnnot_byteRanged
                        exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using hname,
                          hshape, by simpa [NameRanged, StringByteRanged, CharsByteRanged] using hfn,
                          hargs, ihP b (ht' b (by simp)) body hb⟩
          case nd.handle =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | nil => simp only [convProg] at h; exact hnonrec _ ht p h
                | cons c rest3 =>
                  cases rest3 with
                  | nil => simp only [convProg] at h; exact hnonrec _ ht p h
                  | cons d rest4 =>
                    cases rest4 with
                    | nil => simp only [convProg] at h; exact hnonrec _ ht p h
                    | cons e rest5 =>
                      cases rest5 with
                      | cons f rest6 =>
                        cases rest6 with
                        | cons g rest7 => simp only [convProg] at h; exact hnonrec _ ht p h
                        | nil =>
                          simp only [convProg] at h
                          cases hr : convRet a with
                          | none => simp_all
                          | some ret =>
                            cases ret with
                            | none => simp_all
                            | some target =>
                              cases hf : convIdent b with
                              | none => simp_all
                              | some function =>
                                cases ha : convArgList ofInt m c with
                                | none => simp_all
                                | some args =>
                                  cases hx : convIdent d with
                                  | none => simp_all
                                  | some exception =>
                                    cases hbn : convIdent e with
                                    | none => simp_all
                                    | some bound =>
                                      cases hbody : convProg ofInt locations m f with
                                      | none => simp_all
                                      | some handler =>
                                        simp [hr, hf, ha, hx, hbn, hbody] at h
                                        subst h
                                        apply addLocsAnnot_byteRanged
                                        refine ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' b (by simp)) hf,
                                          convArgList_byteRanged ofInt m (fun g _ => convExp_byteRanged ofInt g) c (ht' c (by simp)) args ha, ?_⟩
                                        cases target with
                                        | none =>
                                          refine ⟨trivial,
                                            by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' d (by simp)) hx,
                                            by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' e (by simp)) hbn,
                                            ihP f (ht' f (by simp)) handler hbody⟩
                                        | some vkpair =>
                                          obtain ⟨vk, name⟩ := vkpair
                                          refine ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using
                                            convRet_byteRanged a (ht' a (by simp)) (some (some (vk, name))) hr vk name rfl,
                                            by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' d (by simp)) hx,
                                            by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' e (by simp)) hbn,
                                            ihP f (ht' f (by simp)) handler hbody⟩
                      | nil => simp only [convProg] at h; exact hnonrec _ ht p h
          case nd.call =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons a rest =>
              cases rest with
              | nil => simp only [convProg] at h; exact hnonrec _ ht p h
              | cons b rest2 =>
                cases rest2 with
                | cons c rest3 =>
                  cases rest3 with
                  | cons d rest4 => simp only [convProg] at h; exact hnonrec _ ht p h
                  | nil =>
                    simp only [convProg] at h
                    cases hr : convRet a with
                    | none => simp_all
                    | some ret =>
                      cases hf : convIdent b with
                      | none => simp_all
                      | some function =>
                        cases ha : convArgList ofInt m c with
                        | none => simp_all
                        | some args =>
                          by_cases hfn : function = addWithCarryName
                          · simp [hr, hf, ha, hfn] at h
                            cases ret with
                            | none => simp_all
                            | some t =>
                              cases t with
                              | none => simp_all
                              | some vkname =>
                                obtain ⟨vk, name⟩ := vkname
                                simp only [Option.some.injEq] at h
                                subst h
                                apply addLocsAnnot_byteRanged
                                refine ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using
                                  convRet_byteRanged a (ht' a (by simp)) (some (some (vk, name))) hr vk name rfl,
                                  convArgList_byteRanged ofInt m (fun g _ => convExp_byteRanged ofInt g) c (ht' c (by simp)) args ha⟩
                          · simp [hr, hf, ha, hfn] at h
                            subst h
                            apply addLocsAnnot_byteRanged
                            unfold ProgByteRanged
                            refine ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using convIdent_byteRanged (ht' b (by simp)) hf,
                              convArgList_byteRanged ofInt m (fun g _ => convExp_byteRanged ofInt g) c (ht' c (by simp)) args ha, ?_⟩
                            cases ret with
                            | none => exact trivial
                            | some t =>
                              cases t with
                              | none => simp
                              | some vkname =>
                                obtain ⟨vk, name⟩ := vkname
                                simp only [Option.map_some]
                                exact ⟨by simpa [NameRanged, StringByteRanged, CharsByteRanged] using
                                  convRet_byteRanged a (ht' a (by simp)) (some (some (vk, name))) hr vk name rfl, trivial⟩
                | nil => simp only [convProg] at h; exact hnonrec _ ht p h
          case nd.prog =>
            cases children with
            | nil => simp only [convProg] at h; exact hnonrec _ ht p h
            | cons first rest =>
              simp only [convProg] at h
              exact ihS (first :: rest) (fun t hmem => ht' t hmem) p h
          all_goals (simp only [convProg] at h; exact hnonrec _ ht p h)
      refine ⟨hP, ?_⟩
      intro trees
      induction trees with
      | nil =>
        intro ht p h
        rw [convProgSeq.eq_1] at h
        simp at h
      | cons t ts ihT =>
        cases ts with
        | nil =>
          intro ht p h
          rw [convProgSeq.eq_2] at h
          exact hP t (ht t (by simp)) p h
        | cons u us =>
          intro ht p h
          rw [convProgSeq.eq_3] at h
          · cases hf : convProg ofInt locations (m + 1) t with
            | none => simp_all
            | some first =>
              cases hr : convProgSeq ofInt locations (m + 1) (u :: us) with
              | none => simp_all
              | some rest =>
                simp [hf, hr] at h
                subst h
                exact ⟨hP t (ht t (by simp)) first hf,
                  ihT (fun x hx => ht x (by simp [hx])) rest hr⟩
          · simp

theorem convProg_byteRanged {width : Nat} (ofInt : Int → BitVec width) (locations : Bool)
    (fuel : Nat) :
    ∀ tree, ParseTreeByteRanged tree → ∀ p, convProg ofInt locations fuel tree = some p →
      ProgByteRanged p :=
  (convProg_convProgSeq_byteRanged ofInt locations fuel).1

theorem convProgSeq_byteRanged {width : Nat} (ofInt : Int → BitVec width) (locations : Bool)
    (fuel : Nat) :
    ∀ trees, (∀ t ∈ trees, ParseTreeByteRanged t) → ∀ p,
      convProgSeq ofInt locations fuel trees = some p → ProgByteRanged p :=
  (convProg_convProgSeq_byteRanged ofInt locations fuel).2

theorem convTopDec_byteRanged {width : Nat} (ofInt : Int → BitVec width) (locations : Bool)
    (fuel : Nat) :
    ∀ tree, ParseTreeByteRanged tree → ∀ d, convTopDec ofInt locations fuel tree = some d →
      DeclByteRanged d := by
  intro tree ht decl h
  unfold convTopDec at h
  split at h
  · rename_i inlineTree exportTree shapeTree nameTree paramsTree bodyTree hargs
    cases hpl : paramsTree.argsNT .paramList with
    | none => simp [hpl] at h
    | some pchildren =>
      cases hp : convParams fuel pchildren with
      | none => simp [hpl, hp] at h
      | some params =>
        cases hb : convProg ofInt locations fuel bodyTree with
        | none => simp [hpl, hp, hb] at h
        | some body =>
          cases hn : convIdent nameTree with
          | none => simp [hpl, hp, hb, hn] at h
          | some name =>
            cases hi : convInline inlineTree with
            | none => simp [hpl, hp, hb, hn, hi] at h
            | some inline =>
              cases he : convExport exportTree with
              | none => simp [hpl, hp, hb, hn, hi, he] at h
              | some exported =>
                cases hs : convShape fuel shapeTree with
                | none => simp [hpl, hp, hb, hn, hi, he, hs] at h
                | some returnShape =>
                  simp [hpl, hp, hb, hn, hi, he, hs] at h
                  subst h
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simpa [NameRanged, StringByteRanged, CharsByteRanged]
                      using convIdent_byteRanged
                        (argsNT_byteRanged ht hargs nameTree (by simp)) hn
                  · exact convParams_byteRanged fuel pchildren
                      (argsNT_byteRanged
                        (argsNT_byteRanged ht hargs paramsTree (by simp)) hpl) params hp
                  · exact convProg_byteRanged ofInt locations fuel bodyTree
                      (argsNT_byteRanged ht hargs bodyTree (by simp)) body hb
                  · exact convShape_byteRanged fuel shapeTree
                      (argsNT_byteRanged ht hargs shapeTree (by simp)) returnShape hs
  · cases hd : convDecForm ofInt fuel .globalDec tree with
    | none =>
      simp only [hd] at h
      cases hs : convStructName fuel tree with
      | none =>
        simp only [hs] at h
        cases he : convExnDec fuel tree with
        | none => simp [he] at h
        | some r =>
          simp only [he, Option.some.injEq] at h
          subst h
          obtain ⟨exception, shape⟩ := r
          exact ⟨(convExnDec_byteRanged fuel tree ht _ he).1,
            (convExnDec_byteRanged fuel tree ht _ he).2⟩
      | some r =>
        simp only [hs, Option.some.injEq] at h
        subst h
        obtain ⟨name, fields⟩ := r
        exact ⟨(convStructName_byteRanged ht _ hs).1, (convStructName_byteRanged ht _ hs).2⟩
    | some r =>
      simp only [hd, Option.some.injEq] at h
      subst h
      obtain ⟨shape, name, value⟩ := r
      exact ⟨(convDecForm_byteRanged ofInt fuel .globalDec tree ht _ hd).1,
        (convDecForm_byteRanged ofInt fuel .globalDec tree ht _ hd).2.1,
        (convDecForm_byteRanged ofInt fuel .globalDec tree ht _ hd).2.2⟩

theorem convTopDecList_byteRanged {width : Nat} (ofInt : Int → BitVec width)
    (locations : Bool) :
    ∀ fuel, ∀ tree, ParseTreeByteRanged tree → ∀ ds,
      convTopDecList ofInt locations fuel tree = some ds → ∀ d ∈ ds, DeclByteRanged d := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind n ih =>
    intro tree ht ds h d hd
    cases n with
    | zero => simp [convTopDecList] at h
    | succ m =>
      unfold convTopDecList at h
      split at h
      · -- some []
        rename_i hargs
        simp only [Option.some.injEq] at h
        subst h
        simp at hd
      · -- some [itemTree, restTree]
        rename_i itemTree restTree hargs
        cases ha : destAnnotTok itemTree with
        | some _ =>
          simp [ha] at h
          exact ih m (by omega) restTree
            (argsNT_byteRanged ht hargs restTree (by simp)) ds h d hd
        | none =>
          cases hdec : convTopDec ofInt locations m itemTree with
          | none => simp [ha, hdec] at h
          | some dcl =>
            cases hrest : convTopDecList ofInt locations m restTree with
            | none => simp [ha, hdec, hrest] at h
            | some restDecls =>
              simp [ha, hdec, hrest] at h
              subst h
              rw [List.mem_cons] at hd
              rcases hd with rfl | htail
              · exact convTopDec_byteRanged ofInt locations m itemTree
                  (argsNT_byteRanged ht hargs itemTree (by simp)) _ hdec
              · exact ih m (by omega) restTree
                  (argsNT_byteRanged ht hargs restTree (by simp)) restDecls hrest d htail
      · -- no match
        simp at h


end Flapjack.Parser
