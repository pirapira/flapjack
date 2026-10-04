import Flapjack.Pancake.Proofs.PanToWord.InitialComposition
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
import Flapjack.Pancake.Proofs.PanToCrep.FirstCompileProgAllDistinct
import Flapjack.Pancake.Proofs.PanGlobals.CompileLocalised
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopNames
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
set_option autoImplicit false
namespace Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
/-- Canonical roundtrip for the four source finite maps named by the theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical roundtrip for the target store finite map named by the theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C σ : Type} :
    (∀ (state : WordSemStateBroad width C σ) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C σ,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Full original `state_rel_imp_semantics` (source lines 529-684): all 24
conjuncts, the native word heap length, independent configuration and FFI
carriers, and faithful Word/Pan declaration semantics are retained. The proof
composes the reviewed PanSimp, PanStructs, PanGlobals, PanToCrep, CrepToLoop,
and LoopToWord results, deriving their relations and guards internally.

The relation qualifier names only the canonical finite maps traversed by
these hypotheses; the target code and locals retain native Spt tree maps.
The word qualifier translates the positive HOL type dimension to BitVec width.
This proof-side theorem does not route the executed compiler through the
reviewed pipeline; that production obligation remains on bead .19.3. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
      PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem panToWordStateRelImpSemantics {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width) :
    ((∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail) →
    WordSemStateFiniteExact.semantics target firstLoopName =
      PanSemStateFiniteExact.semanticsDecls source start code := by
  classical
  intro ⟨hmem, hnolabels, hstart, hsize, hparams, hmdomain, hshdomain, hbe, hffi,
    hcurrheap, hheaplen, htop, hdist, halign, halloc, hcode, htcode, hglobals,
    hlocals, heids, heshapes, hloc0, hdim, hfail⟩
  have hglobalsSem := InitialComposition.initialToGlobalsSemantics source target code start globalsSize hfail hdist
    hcode hlocals hglobals heshapes hsize halloc halign hdim hmem
  let structCode := Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)
  let panCode := compileTopExactHOL structCode start
  let globalState : PanSemStateFiniteExact width σ :=
    { source with
      topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
      memaddrs := fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
      memory := wlocWlabHOL ∘ target.memory
      locals := source.locals }
  have hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail := by
    rw [← hglobalsSem]; exact hfail
  let crepState := crepStateHOL globalState panCode globalState.memory
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start structCode ≠ .fail := by
    have h := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
      source start (panSimpDeclsHOL code)
    -- Obtain the same exact prefix without adding a public premise.
    have hs := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
      ⟨(by refine ⟨?_, (fun _ h => h), ?_⟩
           · cases source; rfl
           · intro f vs p sh he; simp [hcode, HolFiniteMapExact.empty] at he), hdist, hcode, hcode, hfail⟩
    have he := h ⟨(by rw [← hs]; exact hfail), hlocals, hcode, hglobals⟩
    have hm : source.eshapes.map2 (fun entry =>
        Pancake.PanStructs.CompileShapeExact.compileShapeExact
          (Pancake.PanStructs.CompileShapeExact.getNamesExact
            { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs entry.2) = source.eshapes := by
      rw [heshapes]; apply HolFiniteMapExact.ext; rfl
    rw [hm] at he
    rw [← he, ← hs]; exact hfail
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  obtain ⟨mainBody, mainShape, hmain⟩ := semanticsDeclsHasMainPanToWordHOL source start structCode
    ⟨hcode, hdiststruct, hstructnf⟩
  have hpanSize : sizeOfEidsHOL panCode < 2 ^ width := by
    dsimp only [panCode]
    rw [sizeOfEidsCompileTopHOL structCode start [] mainBody mainShape hmain]
    dsimp only [structCode]
    rw [sizeOfEidsStructsCompileEqHOL, sizeOfEidsHOL_panSimpDeclsHOL_eq]
    exact heids
  have hcrep := PanToCrepStateRelImpSemanticsTop.stateRelImpSemanticsDeclsPanToCrep
    globalState crepState panCode start
    ⟨(by simp [panToCrepStateRelFiniteExact, crepState, crepStateHOL,
          globalState, hglobals, HolFiniteMapExact.empty]),
      allDistinctCompileTopHOL start structCode hdiststruct,
      hcode, rfl, hlocals, heshapes, compileTopLocalisedHOL structCode start,
      (by apply List.all_eq_true.mpr
          intro d hd
          rcases PanGlobalsCompileDecsStructural.compile_top_only_functions_or_exnsHOL structCode start d hd with h | h <;> simp [h]),
      hpanSize, hglobalnf⟩
  let crepCode := compileProgDeclsHOLW panCode
  let loopState := loopStateHOL crepState arch crepCode target.clock target.memory
  have hcrepnf : crepSemantics crepState start ≠ .fail := by
    rw [hcrep]; exact hglobalnf
  have hmf : (crepToLoopMakeFuncsExactHOL crepCode).lookup start = some (firstLoopName, 0) :=
    flookupMakeFuncsMainHOL structCode start mainBody mainShape hmain
  have hloop := crepToLoopStateRelImpSemantics crepState loopState crepCode start firstLoopName arch
    ⟨(by simp [loopState, loopStateHOL]), rfl,
      (by simp [loopState, loopStateHOL]), rfl, rfl, rfl,
      (by intro address ha
          have ha' : target.mdomain address = true := by
            exact (congrFun hmdomain address).symm ▸ ha
          obtain ⟨w, hw⟩ := hnolabels address ha'
          simp [crepState, crepStateHOL, globalState, loopState, loopStateHOL,
            wlocWlabHOL, wlabWlocExact, hw]),
      (by intro address value he
          simp [crepState, crepStateHOL, HolFiniteMapExact.empty] at he),
      panToCrepFirstCompileProgAllDistinctExact panCode (allDistinctCompileTopHOL start structCode hdiststruct),
      rfl, rfl, rfl, hmf, hcrepnf⟩
  have hloopnf : LoopSemStateFiniteExact.semantics loopState firstLoopName ≠ .fail := by
    rw [hloop]; exact hcrepnf
  have hdm : loopState.mdomain = target.mdomain := by
    funext address
    have hd := congrFun hmdomain address
    apply Bool.eq_iff_iff.mpr
    simpa [loopState, loopStateHOL, crepState, crepStateHOL, globalState] using Iff.of_eq hd.symm
  have hsh : loopState.shMdomain = target.shMdomain := by
    funext address
    have hd := congrFun hshdomain address
    simp [loopState, loopStateHOL, crepState, crepStateHOL, globalState, ← hd]
  have htop' : loopState.topAddr = loopState.baseAddr + (2 : BitVec width) * heapLen := by
    change source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize = _
    rw [htop]
    exact BitVec.sub_add_cancel _ _
  have hcodeWord : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch crepCode)) := by
    simpa [panToWordCompileProgHOL, crepCode, panCode, structCode, hstart, loopToWordCompileHOL] using htcode
  have hparamsLoop := crepToLoopCompileProgDistinctParamsHOLExact crepCode arch
    (compileProgDeclsHOLW_params_nodup panCode)
  have hrelation : loopToWordStateRelHOLExact loopState target := by
    refine ⟨heapLen, rfl, hdm.symm, hsh.symm, rfl, hbe, hffi, hcurrheap, hheaplen, htop', ?_, ?_⟩
    · intro name value hl
      simp [loopState, loopStateHOL, HolFiniteMapExact.empty] at hl
    · intro name params body hl
      constructor
      · rw [hcodeWord]
        exact loopToWordLookupProgSomeLookupCompileProg _ name params body hl
      · apply of_decide_eq_true
        apply (List.all_eq_true.mp hparamsLoop) (name, params, body)
        apply sptAListLookup_mem name (compileProgHOLExact arch crepCode) (params, body)
        simpa only [loopState, loopStateHOL, sptLookup_sptFromAList] using hl
  exact (stateRelImpSemantics loopState target firstLoopName
    ⟨hrelation, rfl, hdim, hloc0, lookupFirstNameCompileProgMainHOL arch crepCode (by simpa [hstart] using hmf), hloopnf⟩).trans
    (hloop.trans (hcrep.trans hglobalsSem.symm))
end Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
