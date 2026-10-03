import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExact
import Flapjack.Pancake.Semantics.PanProps.PanSemIsWrapper
import Flapjack.Pancake.Semantics.PanProps.SemanticsWrapperEquality
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockIoEventsMono

namespace Flapjack.Pancake.Proofs.PanStructs.SemanticsEq
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported state-carrier roundtrip for the four translated fields.
Flapjack representation infrastructure, not a separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full original observational semantics equality. All eight hypotheses remain:
non-Fail, source struct context, empty locals, global fields/wellformedness,
empty context locals, global shape map, and wellformed struct information.
The full compiler theorem matches entry calls at the same clock; the original
clock lemmas discharge all stability/prefix obligations of the original wrapper
equality. No target run, trace equality, evaluator hook or caller IH is assumed.
Executed production routing remains separately tracked. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "semantics_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsEq {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (start : MlS) (context : ContextExact) :
    (PanSemStateFiniteExact.semantics source start ≠ .fail ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      source.locals = HolFiniteMapExact.empty ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      context.locals = [] ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      structInfosOkHOLExact source.structs) →
    PanSemStateFiniteExact.semantics (convertStateExact context source) start =
      PanSemStateFiniteExact.semantics source start := by
  intro ⟨hfail, hstructs, hlocals, hfields, hwf, hclocals, hglobals, hinfos⟩
  let classify : Option (PanSemResultExact width) → SemanticsRunResHOL HolOutcome :=
    fun res => match res with
      | some .timeOut => .Incomplete
      | some (.finalFfi e) => .CompleteResult (.ffiOutcome e)
      | some (.returned _) => .CompleteResult .success
      | _ => .RunError
  let run (state : PanSemStateFiniteExact width σ) :=
    Prod.map classify (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
      fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { state with clock := k }
        (.call none start [] : ProgHOL width)
  rw [panPropsPanSemIsWrapper] at hfail
  rw [panPropsPanSemIsWrapper, panPropsPanSemIsWrapper]
  change panPropsSemanticsWrapper (run (convertStateExact context source)) =
    panPropsSemanticsWrapper (run source)
  change panPropsSemanticsWrapper (run source) ≠ .fail at hfail
  have stable : ∀ (state : PanSemStateFiniteExact width σ) k k' r ev,
      run state k = (r, ev) → r ≠ .Incomplete → run state (k + k') = (r, ev) := by
    intro state k k' r ev he hr
    simp only [run, Function.comp_apply, Prod.map] at he ⊢
    rcases hev : PanSemStateFiniteExact.evaluateHOLFiniteState { state with clock := k }
      (.call none start [] : ProgHOL width) with ⟨res, post⟩
    rw [hev] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨hclass, rfl⟩ := he
    have hnot : res ≠ some .timeOut := by
      intro h
      subst h
      exact hr hclass.symm
    have hadd := panPropsEvaluateAddClockEq _ { state with clock := k } res post k' ⟨hev, hnot⟩
    simp only at hadd
    rw [hadd]
    exact Prod.ext hclass rfl
  have hpref : ∀ (state : PanSemStateFiniteExact width σ) k k' ev,
      run state (k + k') = (.Incomplete, ev) →
      ∃ r' ev', run state k = (r', ev') ∧ ev' <+: ev := by
    intro state k k' ev he
    refine ⟨_, _, rfl, ?_⟩
    have hev := (congrArg Prod.snd he).symm
    simp only [run, Function.comp_apply, Prod.map] at hev ⊢
    rw [hev]
    exact panPropsEvaluateAddClockIoEventsMono (.call none start []) { state with clock := k } k'
  apply panPropsSemanticsWrapper_eq _ _ hfail
  · intro k r ev he hr
    simp only [run, Function.comp_apply, Prod.map] at he
    rcases hev : PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width) with ⟨res, post⟩
    rw [hev] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨hclass, rfl⟩ := he
    have hnot : res ≠ some .error := by
      intro h
      subst h
      exact hr hclass.symm
    have hlocalfields : feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals := by
      simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
    have hlocalwf : feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals := by
      simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
    have hlocalmap : shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
      rw [hclocals, hlocals]
      apply HolFiniteMapExact.ext
      rfl
    have hsim := CompileCorrectExact.compileCorrectExact (.call none start [])
      { source with clock := k } post context res
      ⟨hev, hstructs, hlocalfields, hfields, hlocalwf, hwf, hinfos, hlocalmap, hglobals, hnot⟩
    obtain ⟨hrun, _⟩ := hsim
    have hcomp : compileProgExact context (.call none start [] : ProgHOL width) = .call none start [] := by
      simp [compileProgExact, compileExpsExact]
    rw [hcomp] at hrun
    have hc : convertStateExact context { source with clock := k } =
        { convertStateExact context source with clock := k } := rfl
    rw [hc] at hrun
    refine ⟨0, ?_⟩
    simp only [run, Function.comp_apply, Prod.map, Nat.add_zero]
    rw [hrun]
    rw [← hclass]
    apply Prod.ext
    · rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> rfl
    · rfl
  · exact stable _
  · exact stable _
  · exact hpref _
  · exact hpref _

end Flapjack.Pancake.Proofs.PanStructs.SemanticsEq
