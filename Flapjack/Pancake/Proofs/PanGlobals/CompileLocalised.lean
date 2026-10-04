import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.Semantics.PanProps.LocalisedExpSimps

/-!
The original pan_globals localisation lemmas (`pan_globalsProofScript.sml:3196-3275`):
every expression and program produced by the exact `compile_exp`/`compile`,
`compile_decs` and `compile_top` is `localised`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- `localised_exp` is `every_exp` of the named localisation predicate.
Flapjack infrastructure; no HOL original. -/
theorem localisedExpHOL_eq_every {width : Nat} [NeZero width] :
    (localisedExpHOL : ExpHOL width → Bool) = everyExpHOL localisedExpPredHOL := by
  unfold localisedExpHOL
  congr 1

/-- Exact HOL `compile_exp_localised` (`pan_globalsProofScript.sml:3196-3212`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_localised"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpLocalisedHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (e : ExpHOL width),
      localisedExpHOL (compileExpExactHOL ctxt e) = true := by
  intro ctxt e
  rw [localisedExpHOL_eq_every]
  induction e using compileExpExactHOL.induct ctxt
    (motive2 := fun es =>
      everyExpListHOL localisedExpPredHOL (compileExpExactHOLList ctxt es) = true) <;>
    (try rw [compileExpExactHOL]) <;> (try rw [compileExpExactHOLList]) <;>
    (try split) <;> simp_all [everyExpHOL, everyExpListHOL, localisedExpPredHOL]

/-- Every subexpression of a compiled expression list is localised (the
`EVERY localised_exp` argument folds of `localised_prog`). Flapjack
infrastructure; no HOL original. -/
theorem compileExpListEveryLocalised {width : Nat} [NeZero width]
    (ctxt : PanGlobalsContextExact width) :
    ∀ (es : List (ExpHOL width)),
      everyExpListHOL localisedExpHOL (compileExpExactHOLList ctxt es) = true := by
  have hloc := compileExpLocalisedHOL ctxt
  have hlocList : ∀ es : List (ExpHOL width),
      everyExpListHOL localisedExpPredHOL (compileExpExactHOLList ctxt es) = true := by
    intro es
    induction es with
    | nil => simp [compileExpExactHOLList, everyExpListHOL]
    | cons e es ih =>
      have := hloc e
      rw [localisedExpHOL_eq_every] at this
      simp [compileExpExactHOLList, everyExpListHOL, this, ih]
  intro es
  induction es using compileExpExactHOLList.induct ctxt
    (motive1 := fun e => everyExpHOL localisedExpHOL (compileExpExactHOL ctxt e) = true) <;>
    (try rw [compileExpExactHOL]) <;> (try rw [compileExpExactHOLList]) <;>
    (try split) <;>
    simp_all [everyExpHOL, everyExpListHOL, localisedExpHOL_eq_every, localisedExpPredHOL]

/-- First genuine conjunct of HOL `localised_exp_shape_val`
(`pan_globalsProofScript.sml:3207-3212`): arbitrary shapes build localised
expressions at the original positive word dimension. The complete conjunction
is assembled below as `localisedExpShapeValHOL`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "localised_exp_shape_val"
  (words_as_type_indexed_bitvec)]
theorem shapeValLocalised {width : Nat} [NeZero width] :
    ∀ sh : ShapeHOL, localisedExpHOL (shapeValHOL sh : ExpHOL width) = true := by
  intro sh
  rw [localisedExpHOL_eq_every]
  induction sh using shapeValHOL.induct
    (motive2 := fun shs => everyExpListHOL localisedExpPredHOL
      (shapeValsHOL (width := width) shs) = true) <;>
    (try rw [shapeValHOL]) <;> (try rw [shapeValsHOL]) <;>
    simp_all [everyExpHOL, everyExpListHOL, localisedExpPredHOL]

/-- Full HOL `localised_exp_shape_val` (source lines 3207-3212), with both
universally quantified expression and expression-list conjuncts. HOL `EVERY`
is native `List.all = true`; the reviewed mutual `shape_val`/`shape_vals`
definitions and the exact positive-width expression carrier are used directly.
No source premise or component of the original conjunction is omitted. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "localised_exp_shape_val"
  (words_as_type_indexed_bitvec)]
theorem localisedExpShapeValHOL {width : Nat} [NeZero width] :
    (∀ shape : ShapeHOL, localisedExpHOL (shapeValHOL shape : ExpHOL width) = true) ∧
    (∀ shapes : List ShapeHOL,
      (shapeValsHOL shapes : List (ExpHOL width)).all localisedExpHOL = true) := by
  constructor
  · exact shapeValLocalised
  · intro shapes
    simp [shapeValLocalised]

/-- Exact HOL `compile_localised` (`pan_globalsProofScript.sml:3214-3224`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_localised"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileLocalisedHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (body : ProgHOL width),
      localisedProgHOL (compileProgExactHOL ctxt body) = true := by
  intro ctxt body
  have hE := compileExpLocalisedHOL ctxt
  have hL := compileExpListEveryLocalised ctxt
  have hS := shapeValLocalised (width := width)
  induction body using compileProgExactHOL.induct ctxt
  case case30 =>
    rename_i p h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    cases p with
    | skip => exact (h1 rfl).elim
    | dec a b c d => exact (h2 a b c d rfl).elim
    | assign k n v => cases k <;> first | exact (h3 n v rfl).elim | exact (h4 n v rfl).elim
    | primitive a b c => exact (h5 a b c rfl).elim
    | store a b => exact (h6 a b rfl).elim
    | store32 a b => exact (h7 a b rfl).elim
    | storeByte a b => exact (h8 a b rfl).elim
    | seq a b => exact (h9 a b rfl).elim
    | ite a b c => exact (h10 a b c rfl).elim
    | «while» a b => exact (h11 a b rfl).elim
    | call a b c => exact (h12 a b c rfl).elim
    | decCall a b c d e => exact (h13 a b c d e rfl).elim
    | extCall a b c d e => exact (h14 a b c d e rfl).elim
    | raise a b => exact (h15 a b rfl).elim
    | «return» a => exact (h16 a rfl).elim
    | shMemLoad a k n b => cases k <;> first | exact (h17 a n b rfl).elim | exact (h18 a n b rfl).elim
    | shMemStore a b c => exact (h19 a b c rfl).elim
    | «break» | «continue» | tick | annot _ _ =>
      rw [compileProgExactHOL] <;> simp_all [localisedProgHOL]
  all_goals
    rw [compileProgExactHOL]
    (repeat' split) <;>
      simp_all [localisedProgHOL, localisedExpHOL_eq_every, everyExpHOL, everyExpListHOL,
        localisedExpPredHOL]

/-- Exact HOL `compile_decs_localised` (`pan_globalsProofScript.sml:3226-3234`);
`EVERY (localised_prog ∘ FST o SND ∘ SND)` is membership quantification over
each function's body. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileDecsLocalisedHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width)),
      ∀ e ∈ functionsHOL (compileDecsExactHOL ctxt code).2.1, localisedProgHOL e.2.2.1 = true := by
  intro ctxt code
  induction code generalizing ctxt with
  | nil => simp [compileDecsExactHOL, functionsHOL]
  | cons d ds ih =>
    cases d <;> simp only [compileDecsExactHOL, functionsHOL, List.mem_cons, forall_eq_or_imp]
    all_goals first
      | exact ih _
      | exact ⟨compileLocalisedHOL ctxt _, ih _⟩

/-- Exact HOL `compile_decs_localised'` (`pan_globalsProofScript.sml:3236-3244`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised'"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileDecsLocalisedPrimeHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width)),
      ∀ e ∈ functionsHOL (compileDecsExactHOL ctxt code).2.2.1,
        localisedProgHOL e.2.2.1 = true := by
  intro ctxt code e he
  rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl,
    PanGlobalsDeclListExact.functions_FILTER_exn_declHOL] at he
  simp at he

/-- Exact HOL `compile_decs_localised_main` (`pan_globalsProofScript.sml:3246-3254`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised_main"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileDecsLocalisedMainHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : List (DeclHOL width)),
      ∀ p ∈ (compileDecsExactHOL ctxt code).1, localisedProgHOL p = true := by
  intro ctxt code
  induction code generalizing ctxt with
  | nil => simp [compileDecsExactHOL]
  | cons d ds ih =>
    cases d <;> simp only [compileDecsExactHOL, List.mem_cons, forall_eq_or_imp]
    all_goals first
      | exact ih _
      | exact ⟨by simp [localisedProgHOL, compileExpLocalisedHOL, localisedExpHOL_eq_every,
          everyExpHOL, everyExpListHOL, localisedExpPredHOL] , ih _⟩

/-- Exact HOL `nested_seqs_localised` (`pan_globalsProofScript.sml:3256-3261`);
`EVERY` over the Boolean predicate is `List.all`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "nested_seqs_localised"
  (words_as_type_indexed_bitvec)]
theorem nestedSeqsLocalisedHOL {width : Nat} [NeZero width] :
    ∀ (ps : List (ProgHOL width)), localisedProgHOL (nestedSeqHOL ps) = ps.all localisedProgHOL := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [nestedSeqHOL, localisedProgHOL, ih]

/-- Exact HOL `compile_top_localised` (`pan_globalsProofScript.sml:3263-3276`);
`EVERY (localised_prog ∘ FST o SND ∘ SND)` is membership quantification over
each function's body. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_localised"
  (words_as_type_indexed_bitvec)]
theorem compileTopLocalisedHOL {width : Nat} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)) (main : MlS),
      ∀ e ∈ functionsHOL (compileTopExactHOL pan_code main), localisedProgHOL e.2.2.1 = true := by
  intro pan_code main
  unfold compileTopExactHOL
  rw [compileTopFunctionLookup_eq_lookup]
  cases hl : (functionsHOL pan_code).lookup main with
  | none => simp [functionsHOL]
  | some x =>
    obtain ⟨args, body, rshape⟩ := x
    simp only
    rw [functionsHOL_append,
      PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl,
      PanGlobalsDeclListExact.functions_FILTER_exn_declHOL]
    simp only [functionsHOL, List.nil_append, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, compileDecsLocalisedHOL _ _⟩
    have hargs : ∀ xs : List (MlS × ShapeHOL),
        everyExpListHOL localisedExpHOL
          (xs.map (fun entry => (ExpHOL.var .local entry.1 : ExpHOL width))) = true := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        rw [localisedExpHOL_eq_every] at ih ⊢
        simp [everyExpListHOL, everyExpHOL, localisedExpPredHOL, ih]
    have hinit := compileDecsLocalisedMainHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
           ((decShapesHOL (fpermDecsHOL main (newMainNameHOL pan_code)
             (resortDeclsHOL pan_code))).map sizeOfShapeHOL).sum } : PanGlobalsContextExact width)
      (fpermDecsHOL main (newMainNameHOL pan_code) (resortDeclsHOL pan_code))
    simp only [localisedProgHOL, nestedSeqsLocalisedHOL, hargs, Bool.and_true, List.all_eq_true]
    exact hinit

namespace PanGlobalsCompileLocalisedWitnesses

/-- Canonical roundtrip of the pan_globals context carrier, re-exported for the
`fmap_as_finite_support_relation := [PanGlobalsContextExact.globals]`
qualifiers of this module. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

end PanGlobalsCompileLocalisedWitnesses

end Flapjack
