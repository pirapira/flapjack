import Flapjack.Parser.Localise
import Flapjack.Parser.GrammarByteRanged

/-!
Byte-rangedness is preserved by the localisation pass.

`localiseExp`, `localiseProg` and `localiseDecl` only reclassify the
`VarKind` of variable occurrences; they never change identifiers, shapes or
literals.  So the byte-rangedness predicates established for converted parse
trees survive localisation, which is the last step of `parseTopDecs` before it
returns declarations to the caller.
-/

namespace Flapjack.Parser

open Flapjack
open Flapjack.Pancake.PanLang

theorem localiseExp_byteRanged {width : Nat} :
    ∀ scope : List VarName,
      (∀ expressions : List (Exp (BitVec width)),
          ListExpByteRanged expressions →
          ListExpByteRanged (localiseExp.localiseExps scope expressions)) ∧
      (∀ expression : Exp (BitVec width),
          ExpByteRanged expression →
          ExpByteRanged (localiseExp scope expression)) ∧
      (∀ fields : List (FieldName × Exp (BitVec width)),
          ListFieldByteRanged fields →
          ListFieldByteRanged (localiseExp.localiseFields scope fields)) := by
  intro scope
  have hexpr : ∀ expression : Exp (BitVec width),
      ExpByteRanged expression → ExpByteRanged (localiseExp scope expression) := by
    apply localiseExp.induct
      (motive1 := fun es => ListExpByteRanged es →
        ListExpByteRanged (localiseExp.localiseExps scope es))
      (motive2 := fun e => ExpByteRanged e → ExpByteRanged (localiseExp scope e))
      (motive3 := fun fs => ListFieldByteRanged fs →
        ListFieldByteRanged (localiseExp.localiseFields scope fs))
    · intro h
      simp only [ListExpByteRanged, localiseExp.localiseExps.eq_1]
    · intro expression expressions ihExpr ihExps h
      simp only [ListExpByteRanged, localiseExp.localiseExps.eq_2] at h ⊢
      exact ⟨ihExpr h.1, ihExps h.2⟩
    · intro value _
      simp only [ExpByteRanged, localiseExp]
    · intro kind name h
      simp only [ExpByteRanged, localiseExp]
      exact h
    · intro fields ih h
      simp only [ExpByteRanged, localiseExp]
      exact ih h
    · intro index value ih h
      simp only [ExpByteRanged, localiseExp]
      exact ih h
    · intro name fields ih h
      simp only [ExpByteRanged, localiseExp] at h ⊢
      exact ⟨h.1, ih h.2⟩
    · intro name value ih h
      simp only [ExpByteRanged, localiseExp] at h ⊢
      exact ⟨h.1, ih h.2⟩
    · intro shape address ih h
      simp only [ExpByteRanged, localiseExp] at h ⊢
      exact ⟨h.1, ih h.2⟩
    · intro address h
      simp only [ExpByteRanged, localiseExp]
      exact h
    · intro address ih h
      simp only [ExpByteRanged, localiseExp]
      exact ih h
    · intro operator args ih h
      simp only [ExpByteRanged, localiseExp]
      exact ih h
    · intro operator args ih h
      simp only [ExpByteRanged, localiseExp]
      exact ih h
    · intro operator left right ihL ihR h
      simp only [ExpByteRanged, localiseExp] at h ⊢
      exact ⟨ihL h.1, ihR h.2⟩
    · intro operator left right ihL ihR h
      simp only [ExpByteRanged, localiseExp] at h ⊢
      exact ⟨ihL h.1, ihR h.2⟩
    · intro h
      simp only [ExpByteRanged, localiseExp]
    · intro h
      simp only [ExpByteRanged, localiseExp]
    · intro h
      simp only [ExpByteRanged, localiseExp]
    · intro h
      simp only [ListFieldByteRanged, localiseExp.localiseFields.eq_1]
    · intro name expression fields ihExpr ihFields h
      simp only [ListFieldByteRanged, localiseExp.localiseFields.eq_2] at h ⊢
      exact ⟨h.1, ihExpr h.2.1, ihFields h.2.2⟩
  have hexps : ∀ expressions : List (Exp (BitVec width)),
      ListExpByteRanged expressions →
      ListExpByteRanged (localiseExp.localiseExps scope expressions) := by
    intro expressions
    induction expressions with
    | nil =>
        intro _
        rw [localiseExp.localiseExps.eq_1]
        trivial
    | cons e es ih =>
        intro h
        simp only [ListExpByteRanged] at h
        rw [localiseExp.localiseExps.eq_2]
        simp only [ListExpByteRanged]
        exact ⟨hexpr e h.1, ih h.2⟩
  have hfields : ∀ fields : List (FieldName × Exp (BitVec width)),
      ListFieldByteRanged fields →
      ListFieldByteRanged (localiseExp.localiseFields scope fields) := by
    intro fields
    induction fields with
    | nil =>
        intro _
        rw [localiseExp.localiseFields.eq_1]
        trivial
    | cons p ps ih =>
        intro h
        obtain ⟨name, expression⟩ := p
        simp only [ListFieldByteRanged] at h
        rw [localiseExp.localiseFields.eq_2]
        simp only [ListFieldByteRanged]
        exact ⟨h.1, hexpr expression h.2.1, ih h.2.2⟩
  exact ⟨hexps, hexpr, hfields⟩

theorem localiseExpList_byteRanged {width : Nat} :
    ∀ scope : List VarName, ∀ expressions : List (Exp (BitVec width)),
      ListExpByteRanged expressions →
      ListExpByteRanged (localiseProg.localiseExpList scope expressions) := by
  intro scope expressions
  induction expressions with
  | nil =>
      intro _
      rw [localiseProg.localiseExpList.eq_1]
      trivial
  | cons e es ih =>
      intro h
      simp only [ListExpByteRanged] at h
      rw [localiseProg.localiseExpList.eq_2]
      simp only [ListExpByteRanged]
      exact ⟨(localiseExp_byteRanged scope).2.1 e h.1, ih h.2⟩

theorem localiseExpList_mem_byteRanged {width : Nat} (scope : List VarName)
    (expressions : List (Exp (BitVec width)))
    (h : ∀ e ∈ expressions, ExpByteRanged e) :
    ∀ e ∈ localiseProg.localiseExpList scope expressions, ExpByteRanged e :=
  (listExpByteRanged_iff _).mp
    (localiseExpList_byteRanged scope expressions ((listExpByteRanged_iff expressions).mpr h))

theorem localiseProg_byteRanged {width : Nat} :
    ∀ scope : List VarName, ∀ program : Prog (BitVec width),
      ProgByteRanged program → ProgByteRanged (localiseProg scope program) := by
  apply localiseProg.induct
    (motive := fun sc p => ProgByteRanged p → ProgByteRanged (localiseProg sc p))
  · intro scope h
    simp only [ProgByteRanged, localiseProg] at h ⊢
  · intro scope name shape value body ih h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, h.2.1, (localiseExp_byteRanged scope).2.1 value h.2.2.1, ih h.2.2.2⟩
  · intro scope kind name value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, (localiseExp_byteRanged scope).2.1 value h.2⟩
  · intro scope name operator args h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, localiseExpList_mem_byteRanged scope args h.2⟩
  · intro scope address value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨(localiseExp_byteRanged scope).2.1 address h.1,
      (localiseExp_byteRanged scope).2.1 value h.2⟩
  · intro scope address value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact h
  · intro scope address value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨(localiseExp_byteRanged scope).2.1 address h.1,
      (localiseExp_byteRanged scope).2.1 value h.2⟩
  · intro scope first second ihF ihS h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨ihF h.1, ihS h.2⟩
  · intro scope condition thenBranch elseBranch ihT ihE h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨(localiseExp_byteRanged scope).2.1 condition h.1, ihT h.2.1, ihE h.2.2⟩
  · intro scope condition body ihB h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨(localiseExp_byteRanged scope).2.1 condition h.1, ihB h.2⟩
  · intro scope h
    simp only [ProgByteRanged, localiseProg] at h ⊢
  · intro scope h
    simp only [ProgByteRanged, localiseProg] at h ⊢
  · intro scope name args h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, localiseExpList_mem_byteRanged scope args h.2.1, trivial⟩
  · intro scope target name args h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    refine ⟨h.1, localiseExpList_mem_byteRanged scope args h.2.1, ?_⟩
    cases target with
    | none => exact h.2.2
    | some kv => exact h.2.2
  · intro scope target exception bound handler name args ihHandler h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    refine ⟨h.1, localiseExpList_mem_byteRanged scope args h.2.1, ?_⟩
    cases target with
    | none => exact ⟨trivial, h.2.2.2.1, h.2.2.2.2.1, ihHandler h.2.2.2.2.2⟩
    | some kv => exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ihHandler h.2.2.2.2.2⟩
  · intro scope name shape function args body ihBody h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, localiseExpList_mem_byteRanged scope args h.2.2.2.1,
      ihBody h.2.2.2.2⟩
  · intro scope function configuration configurationLength array arrayLength h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, (localiseExp_byteRanged scope).2.1 configuration h.2.1,
      (localiseExp_byteRanged scope).2.1 configurationLength h.2.2.1,
      (localiseExp_byteRanged scope).2.1 array h.2.2.2.1,
      (localiseExp_byteRanged scope).2.1 arrayLength h.2.2.2.2⟩
  · intro scope exception value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, (localiseExp_byteRanged scope).2.1 value h.2⟩
  · intro scope value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact (localiseExp_byteRanged scope).2.1 value h
  · intro scope size kind name address h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨h.1, (localiseExp_byteRanged scope).2.1 address h.2⟩
  · intro scope size address value h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact ⟨(localiseExp_byteRanged scope).2.1 address h.1,
      (localiseExp_byteRanged scope).2.1 value h.2⟩
  · intro scope h
    simp only [ProgByteRanged, localiseProg] at h ⊢
  · intro scope tag text h
    simp only [ProgByteRanged, localiseProg] at h ⊢
    exact h

theorem localiseDecl_byteRanged {width : Nat} (declaration : Decl (BitVec width))
    (h : DeclByteRanged declaration) : DeclByteRanged (localiseDecl declaration) := by
  cases declaration with
  | function d =>
      simp only [DeclByteRanged, FunDeclByteRanged] at h ⊢
      exact ⟨h.1, h.2.1, localiseProg_byteRanged (d.params.map Prod.fst) d.body h.2.2.1,
        h.2.2.2⟩
  | decl shape name value => exact h
  | exnDecl exceptionName shape => exact h
  | name struct fields => exact h

theorem localiseDecls_byteRanged {width : Nat} (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ localiseDecls declarations, DeclByteRanged d := by
  intro d hd
  simp only [localiseDecls, List.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  exact localiseDecl_byteRanged e (h e he)

end Flapjack.Parser
