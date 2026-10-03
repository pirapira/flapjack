import Flapjack.Pancake.Proofs.PanStructs.SemanticsEq
import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.DecsStcnamesCompileDecls
import Flapjack.Pancake.Proofs.PanStructs.DecsStcnamesNames
namespace Flapjack.Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported broad/state roundtrip for the translated state maps.
Flapjack representation infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full original top-level declaration semantics theorem. The four hypotheses
are non-Fail and empty locals/code/globals. The conclusion uses the faithful
semanticsDecls, exact compileTopExact, and the original eshapes FMAP_MAP2 update.
Only get_names' structs projection is observed in that update; its other initial
fields are immaterial, and the standard compile_top empty initial context is used.
The proof composes the whole declaration theorem, original struct-name lemmas,
and full semantics_eq. No target run/observation or caller relation is assumed.
Production compiler routing remains an independent inventory obligation. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_top_semantics_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileTopSemanticsDeclsExact {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (start : MlS) (code : List (DeclHOL width)) :
    (PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail ∧
      source.locals = HolFiniteMapExact.empty ∧ source.code = HolFiniteMapExact.empty ∧
      source.globals = HolFiniteMapExact.empty) →
    PanSemStateFiniteExact.semanticsDecls source start code =
      PanSemStateFiniteExact.semanticsDecls
        { source with eshapes := source.eshapes.map2 (fun entry =>
          compileShapeExact (getNamesExact { structs := [], locals := [], globals := [] } code).structs entry.2) }
        start (compileTopExact code) := by
  classical
  intro ⟨hfail, hlocals, hcode, hglobals⟩
  rcases hnames : decsStcnamesHOLExact [] code with _ | structs
  · simp [PanSemStateFiniteExact.semanticsDecls, hnames] at hfail
  simp only [PanSemStateFiniteExact.semanticsDecls, hnames] at hfail ⊢
  rcases hev : PanSemStateFiniteExact.evaluateDeclsHOLFinite { source with structs := structs } code with _ | post
  · simp [hev] at hfail
  simp only [hev] at hfail ⊢
  let context := getNamesExact { structs := [], locals := [], globals := [] } code
  have hctx := decsStcnamesToGetNames [] code structs
    ({ structs := [], locals := [], globals := [] } : ContextExact) ⟨hnames, rfl⟩
  have hctxstructs : context.structs = structs.map (fun entry => (entry.1, entry.2.fields)) := by
    simp [context, hctx]
  have hctxlocals : context.locals = [] := by simp [context, hctx]
  have hctxglobals : context.globals = [] := by simp [context, hctx]
  have hinfos := decsStcnamesInfosOk [] code structs ()
    ⟨hnames, by simp [structInfosOkHOLExact]⟩
  have hmapempty : ∀ {α β γ : Type} (f : α × β → γ),
      HolFiniteMapExact.map2 f (HolFiniteMapExact.empty : HolFiniteMapExact α β) = HolFiniteMapExact.empty := by
    intro α β γ f
    apply HolFiniteMapExact.ext
    rfl
  have hfields : feveryHOL (fun entry => valueFldsOkHOLExact structs entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hwf : feveryHOL (fun entry => isWfShapeValueHOLExact structs entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hshapes : shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hctxglobals, hglobals, hmapempty]
    rfl
  rcases hcompile : compileDeclsExact context code with ⟨compiled, finalContext⟩
  have hsim := CompileDeclsCorrectExact.compileDeclsCorrectExact
    { source with structs := structs } code post context finalContext compiled
    ⟨hev, hctxstructs, hctxlocals, hinfos, hfields, hwf, hshapes, hcompile⟩
  obtain ⟨hrun, globals, hfinal, hpostfields, hpostwf, hpoststructs, hpostlocals, hpostshapes⟩ := hsim
  have htop : compileTopExact code = compiled := by
    change (compileDeclsExact context code).1 = compiled
    rw [hcompile]
  have hcompilednames := decsStcnamesCompileDecls context code []
  rw [hcompile] at hcompilednames
  have hboot : convertStateExact finalContext { source with structs := structs } =
      { source with eshapes := source.eshapes.map2 (fun entry =>
          compileShapeExact context.structs entry.2), structs := [] } := by
    simp [convertStateExact, convertCodeExact, convertEshapesExact,
      hlocals, hglobals, hcode, hmapempty, hfinal]
  rw [htop, hcompilednames]
  simp only
  have htargetRun : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with eshapes := source.eshapes.map2 (fun entry =>
          compileShapeExact context.structs entry.2), structs := [] }
      (fun address => Classical.propDecidable (source.memaddrs address)) compiled =
      some (convertStateExact finalContext post) := by
    exact (congrArg (fun state : PanSemStateFiniteExact width σ =>
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
        (fun address => Classical.propDecidable (state.memaddrs address)) compiled)
      hboot).symm.trans hrun
  rw [htargetRun]
  simp only
  symm
  apply SemanticsEq.semanticsEq post start finalContext
  refine ⟨hfail, ?_, ?_, ?_, ?_, ?_, (by simpa [hfinal] using hpostshapes), ?_⟩
  · simpa [hfinal, hpoststructs] using hctxstructs
  · simpa [hpostlocals] using hlocals
  · simpa [hpoststructs] using hpostfields
  · simpa [hpoststructs] using hpostwf
  · simpa [hfinal] using hctxlocals
  · simpa [hpoststructs] using hinfos
end Flapjack.Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact
