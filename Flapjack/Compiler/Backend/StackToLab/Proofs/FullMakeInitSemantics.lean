import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
import Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCode
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
import Flapjack.Compiler.Backend.StackRemove.Proofs.CallArgs
import Flapjack.Compiler.Backend.StackRawCall.Proofs.Conventions
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Conventions

/-! `full_make_init_semantics` (`stack_to_labProofScript.sml:3365-3618`):
the LabSem semantics of the whole stack-to-lab compilation, from a LabSem state
satisfying the memory and register assumptions, equals the StackSem semantics
of the source program from the fully initialized state, and that initialization
succeeds. The proof composes the `make_init_semantics` theorems of
stack_to_lab, stack_names, stack_remove and stack_alloc with rawcall's
`compile_semantics`, as in HOL. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure.
The roundtrip covers all three HOL finite-map fields: registers,
floating-point registers, and the populated initialization store. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- The premises of `full_make_init_semantics` other than the
`full_make_init` equation (Flapjack abbreviation for the proof). -/
def Assumptions {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) : Prop :=
  goodDimindex width ∧
  t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
  t.compileOracle = (fun n => ((coracle n).1,
    StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp (coracle n).2.1)) ∧
  ¬t.failed = true ∧
  MakeInit.memoryAssumption stackConf.regNames bitmaps dataSp t ∧
  StackRemove.maxStackAlloc ≤ maxHeap ∧
  ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
  (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
  (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
  (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
  (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
  GoodCode.goodCode sp code ∧
  (∀ n, GoodCode.goodCode sp (coracle n).2.1) ∧
  10 ≤ sp ∧
  (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
  StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
  StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
  StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
  StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
  StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
  Function.Bijective (StackNames.findNameSpt stackConf.regNames)

section Stages
variable {width : Nat} [NeZero width] {C F : Type}
  (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
  (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
  (code : List (Nat × HolProg width)) (t : Flapjack.Compiler.Backend.LabSem.State width C F)
  (saveRegs : Nat → Bool) (dataSp : Nat)
  (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))

/-- `code1` of `full_make_init_def`. -/
def code1 : List (Nat × HolProg width) :=
  StackAlloc.compile dataConf (StackRawCall.compile code)

/-- `code2` of `full_make_init_def`. -/
def code2 : List (Nat × HolProg width) :=
  StackRemove.compileHOL stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind) maxHeap sp
    BvlToBvi.initGlobalsLocation (code1 dataConf code)

/-- `coracle1` of `full_make_init_def`. -/
def coracle1 : Nat → C × List (Nat × HolProg width) × List (BitVec width) :=
  Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ coracle

/-- `coracle2` of `full_make_init_def`. -/
def coracle2 : Nat → C × List (Nat × HolProg width) × List (BitVec width) :=
  Prod.map id (Prod.map (List.map (StackRemove.progComp stackConf.jump offset sp)) id) ∘
    coracle1 coracle

/-- `coracle3` of `full_make_init_def`. -/
def coracle3 : Nat → C × List (Nat × HolProg width) × List (BitVec width) :=
  Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘
    coracle2 stackConf sp offset coracle

/-- `s3` of `full_make_init_def`. -/
noncomputable def s3 : StackSemStateFiniteExact width C F :=
  MakeInit.makeInit (sptFromAList (StackNames.compileHOL stackConf.regNames
      (code2 stackConf dataConf maxHeap sp offset code)))
    (coracle3 stackConf sp offset coracle)
    ([2, 3, 4].map (StackNames.findNameSpt stackConf.regNames)) saveRegs t

/-- `s2` of `full_make_init_def`. -/
noncomputable def s2 : StackSemStateFiniteExact width C F :=
  StackNames.makeInit stackConf.regNames
    (sptFromAList (code2 stackConf dataConf maxHeap sp offset code))
    (coracle2 stackConf sp offset coracle)
    (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle)

theorem fullMakeInit_eq :
    fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle =
      (StackAlloc.makeInit dataConf (sptFromAList code) coracle
        (StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap
          bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)),
       StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind) maxHeap
          bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)) := rfl

end Stages

/-- `decide` of a true proposition, for whichever instance the term carries. -/
theorem decide_true_of {p : Prop} (inst : Decidable p) (h : p) : @decide p inst = true := by
  cases inst with
  | isFalse hn => exact absurd h hn
  | isTrue _ => rfl

theorem sptDomain_sptFromAList {α : Type} (l : List (Nat × α)) (x : Nat) :
    sptDomain (sptFromAList l) x ↔ x ∈ l.map Prod.fst := by
  simp only [sptDomain, sptLookup_sptFromAList]
  induction l with
  | nil => simp [sptAListLookup]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : x = k
    · subst h; simp [sptAListLookup]
    · simp [sptAListLookup, h, ih]

theorem goodCode_names {width : Nat} [NeZero width] {sp : Nat} {code : List (Nat × HolProg width)}
    (h : GoodCode.goodCode sp code) :
    ∀ n ∈ code.map Prod.fst, n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gcStubLocation := by
  intro n hn
  obtain ⟨⟨n', q⟩, hm, rfl⟩ := List.mem_map.mp hn
  have := (h.2.1 _ hm).1
  simp only [stackNumStubs, gcStubLocation] at this ⊢
  omega

theorem goodCode_labels {width : Nat} [NeZero width] {sp : Nat} {code : List (Nat × HolProg width)}
    (h : GoodCode.goodCode sp code) :
    ∀ np ∈ code, (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
      (StackPropsCodeLabels.extractLabels np.2).Nodup :=
  h.2.2.2.2

section Stage
variable {width : Nat} [NeZero width] {C F : Type}
  {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
  {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
  {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
  {saveRegs : Nat → Bool} {dataSp : Nat}
  {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}

theorem code2_fst :
    (code2 stackConf dataConf maxHeap sp offset code).map Prod.fst =
      0 :: 1 :: 2 :: gcStubLocation :: code.map Prod.fst :=
  CompileLabPres.mapFstCompileCompile

theorem code2_nodup (h : GoodCode.goodCode sp code) :
    ((code2 stackConf dataConf maxHeap sp offset code).map Prod.fst).Nodup := by
  rw [code2_fst]
  have hn := goodCode_names h
  simp only [List.nodup_cons, List.mem_cons, not_or]
  refine ⟨⟨by decide, by decide, by decide, fun m => (hn 0 m).1 rfl⟩,
    ⟨by decide, by decide, fun m => (hn 1 m).2.1 rfl⟩,
    ⟨by decide, fun m => (hn 2 m).2.2.1 rfl⟩, fun m => (hn _ m).2.2.2 rfl, h.1⟩

theorem labelsOk_tcode
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    CodeInstalled.labelsOk t.code := by
  rw [hA.2.1]
  exact CompileLabPres.stackToLabCompileLabPres
    ⟨goodCode_names hA.2.2.2.2.2.2.2.2.2.2.2.2.1, goodCode_labels hA.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hA.2.2.2.2.2.2.2.2.2.2.2.2.1.1⟩

theorem tcode_eq
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    t.code = (StackNames.compileHOL stackConf.regNames
      (code2 stackConf dataConf maxHeap sp offset code)).map progToSectionHOL := hA.2.1

theorem code2_callArgs (h : GoodCode.goodCode sp code) :
    ∀ q ∈ (code2 stackConf dataConf maxHeap sp offset code).map Prod.snd,
      StackProps.callArgs q 1 2 3 4 0 :=
  StackRemove.Proofs.CallArgs.stackRemoveCallArgs
    ⟨rfl, StackAlloc.stack_alloc_call_args (StackRawCall.stackRawcallCallArgs.mpr h.2.2.1)⟩

/-- Renamed `call_args` at the LabSem registers. -/
theorem callArgs_names
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    {q : HolProg width} (hq : StackProps.callArgs q 1 2 3 4 0) :
    StackProps.callArgs (StackNames.progCompHOL stackConf.regNames q) t.ptrReg t.lenReg
      t.ptr2Reg t.len2Reg t.linkReg := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h3, h2, h1, h0, -⟩ := hA
  have := StackNames.callArgs_progCompHOL stackConf.regNames q 1 2 3 4 0 hq
  rwa [h1, h2, h3, h4, h0] at this

theorem stateRel_s3
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    StateRel.stateRel (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle) t := by
  have hok := labelsOk_tcode hA
  have htc := tcode_eq hA
  obtain ⟨gd, -, horacle, hfailed, -, -, hlink, -, hio, hcc, hmd, hsmd, hgood, hgoodO, -, -,
    h4, h3, h2, h1, h0, hbij⟩ := id hA
  refine (MakeInit.stateRelMakeInit).mpr ⟨?_, hfailed, ?_, ?_, ?_, ?_, ?_, ?_, hlink, ?_, ?_,
    hio, hcc, hmd, hsmd, gd⟩
  · intro n prog hl
    rw [sptLookup_sptFromAList, FlattenCorrect.sptAListLookup_eq_holAlookup] at hl
    obtain ⟨pc, hinst, hloc⟩ := CodeInstalled.codeInstalledProgToSection _ n prog
      ⟨by rw [← htc]; exact hok, hl⟩
    refine ⟨?_, pc, by rw [htc]; exact hinst, by rw [htc]; exact hloc⟩
    have hm := CodeInstalled.holAlookup_mem _ _ _ hl
    simp only [StackNames.compileHOL, List.mem_map, StackNames.progCompEntryHOL,
      Prod.mk.injEq] at hm
    obtain ⟨⟨n', q⟩, hq, rfl, rfl⟩ := hm
    exact callArgs_names hA (code2_callArgs hgood q
      (List.mem_map.mpr ⟨_, hq, rfl⟩))
  · rw [horacle]
    funext n
    simp [coracle3, coracle2, coracle1, StackToLab.compileNoStubs, Prod.map, Function.comp_def]
  · intro k
    refine ⟨fun np hnp => ?_, ?_⟩
    · simp only [coracle3, coracle2, coracle1, Function.comp_apply, Prod.map, id,
        StackNames.compileHOL, List.mem_map] at hnp
      obtain ⟨x, ⟨y, ⟨⟨n0, p0⟩, he, rfl⟩, rfl⟩, rfl⟩ := hnp
      obtain ⟨-, hal, hca, -, hlab⟩ := hgoodO k
      have hc0 := hca p0 (List.mem_map.mpr ⟨_, he, rfl⟩)
      obtain ⟨hE, hD⟩ := hlab _ he
      have hap := StackAlloc.stack_alloc_lab_pres n0 (StackAlloc.nextLabHOL p0 2) p0 0
        ⟨hE, hD, Nat.le_refl _⟩
      simp only [StackNames.progCompEntryHOL, StackRemove.progComp, StackAlloc.progComp,
        ← StackNames.stackNamesLabPres, ← StackRemove.Proofs.LabPres.stackRemoveLabPres]
      exact ⟨callArgs_names hA (StackRemove.Proofs.CallArgs.callArgs_comp _ _ _ _
        (StackAlloc.ConventionSupport.comp_callArgs n0 _ p0 hc0)), hap.1, hap.2.1⟩
    · simpa [coracle3, coracle2, coracle1, StackNames.compileHOL, StackNames.progCompEntryHOL,
        StackRemove.progComp, StackAlloc.progComp, List.map_map, Function.comp_def] using
        (hgoodO k).1
  · rw [← h0, ← h2]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h1]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h4]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h3]; exact fun e => absurd (hbij.1 e) (by decide)
  · intro x
    rw [sptDomain_sptFromAList, htc, CodeInstalled.mapProgToSectionFst]
  · exact (CodeInstalled.labelsOkImp _ hok).1

theorem locToPc_start
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    Flapjack.Compiler.Backend.LabSem.locToPc 0 0 t.code = some t.pc := by
  rw [hA.2.2.2.2.2.2.2.1, tcode_eq hA]
  simp only [code2, StackRemove.compileHOL, StackRemove.initStubs, StackNames.compileHOL,
    StackNames.progCompEntryHOL, List.cons_append, List.map_cons, CodeInstalled.progToSection_eq]
  rw [Flapjack.Compiler.Backend.LabSem.locToPc.eq_def]
  simp

/-- The stack_names and stack_to_lab stages: the LabSem semantics is the
semantics of `s2` from procedure 0. -/
theorem stageLab
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    StackSemEvaluate.semantics 0 (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) ≠
        .fail →
      Flapjack.Compiler.Backend.LabSem.semantics t =
        StackSemEvaluate.semantics 0
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
  intro hne
  have hnames : StackSemEvaluate.semantics 0 (s3 stackConf dataConf maxHeap sp offset code t
      saveRegs coracle) =
      StackSemEvaluate.semantics 0
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) :=
    StackNames.makeInitSemantics ⟨by simp [s3, MakeInit.makeInit], by simp [s3, MakeInit.makeInit],
      by simp [s3, MakeInit.makeInit], hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      code2_nodup hA.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl⟩
  rw [← hnames] at hne ⊢
  exact MakeInit.makeInitSemantics ⟨MakeInit.haltAssumLemma, stateRel_s3 hA, locToPc_start hA, hne⟩

theorem s2_fields :
    let st := s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle
    st.code = sptFromAList (code2 stackConf dataConf maxHeap sp offset code) ∧
      st.compileOracle = coracle2 stackConf sp offset coracle ∧
      st.useStack = false ∧ st.useStore = false ∧ st.useAlloc = false ∧
      st.memory = t.memory ∧ st.mdomain = t.memDomain ∧ st.codeBuffer = t.codeBuffer ∧
      st.ffi = t.ffi := by
  simp [s2, s3, StackNames.makeInit, MakeInit.makeInit]

theorem dischargeThese_s2
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    StackRemove.Proofs.InitMake.dischargeThese stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (coracle1 coracle) (code1 dataConf code)
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
  obtain ⟨-, -, -, -, -, hmax, -, -, -, -, -, -, hgood, hgoodO, hsp, hsave, -, -, -, -, -,
    hbij⟩ := id hA
  obtain ⟨hcode, horacle, hus, hust, hua, -⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset) (code := code)
    (t := t) (saveRegs := saveRegs) (coracle := coracle)
  refine ⟨?_, ?_, ?_, hcode, by omega, ?_, ?_, hus, hust, hua, hmax⟩
  · intro entry hmem
    refine ⟨StackAlloc.stack_alloc_reg_bound ⟨hsp, StackRawCall.stackRawcallRegBound.mpr
      hgood.2.2.2.1⟩ entry.2 (List.mem_map.mpr ⟨entry, hmem, rfl⟩), ?_⟩
    simp only [code1, StackAlloc.compile, StackAlloc.stubs, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hmem
    rcases hmem with rfl | ⟨⟨n0, p0⟩, hm, rfl⟩
    · simp [stackNumStubs, gcStubLocation]
    · simp only [StackRawCall.compile, List.mem_map, Prod.mk.injEq] at hm
      obtain ⟨⟨n1, p1⟩, hm1, rfl, -⟩ := hm
      have := (hgood.2.1 _ hm1).1
      simp only [StackAlloc.progComp]
      omega
  · intro n i p hm
    simp only [coracle1, Function.comp_apply, Prod.map, id, List.mem_map] at hm
    obtain ⟨⟨n0, p0⟩, hm0, he⟩ := hm
    simp only [StackAlloc.progComp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, hal, -, hrb, -⟩ := hgoodO n
    refine ⟨StackAlloc.ConventionSupport.comp_regBound hsp _ _ _
      (hrb p0 (List.mem_map.mpr ⟨_, hm0, rfl⟩)), ?_⟩
    have := (hal _ hm0).1
    omega
  · rw [horacle]
    funext n
    simp [coracle2, Prod.map]
  · rw [hcode, sptDomain_sptFromAList, code2_fst]
    simp
  · intro r hr
    have key : ∃ x, saveRegs x = true ∧
        r = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) x := by
      refine ⟨StackNames.findNameSpt stackConf.regNames r, ?_,
        (holLinv_apply_of_injective hbij.1 r).symm⟩
      rcases hr with h | h | h <;> rw [h]
      · have := hsave 2 (by simp); rwa [show 2 + sp - 2 = sp by omega] at this
      · have := hsave 3 (by simp); rwa [show 3 + sp - 2 = sp + 1 by omega] at this
      · have := hsave 4 (by simp); rwa [show 4 + sp - 2 = sp + 2 by omega] at this
    simp only [s2, StackNames.makeInit, s3, MakeInit.makeInit]
    exact decide_true_of _ key

theorem s2_regs_lookup (hbij : Function.Bijective (StackNames.findNameSpt stackConf.regNames))
    {i : Nat} (hi : i = 2 ∨ i = 3 ∨ i = 4) :
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).regs.lookup i =
      some (t.regs (StackNames.findNameSpt stackConf.regNames i)) := by
  have hinv : ∀ y, StackNames.findNameSpt stackConf.regNames
      (holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y) = y :=
    apply_holLinv_of_surjective hbij.2
  have hlinj : Function.Injective
      (holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True)) := by
    intro a b hab; rw [← hinv a, ← hinv b, hab]
  have hi' : i = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True)
      (StackNames.findNameSpt stackConf.regNames i) := (holLinv_apply_of_injective hbij.1 i).symm
  simp only [s2, StackNames.makeInit]
  rw [hi', HolFiniteMapExact.lookup_mapKeys_of_injective hlinj, ← hi']
  have d23 : StackNames.findNameSpt stackConf.regNames 2 ≠
      StackNames.findNameSpt stackConf.regNames 3 :=
    fun e => absurd (hbij.1 e) (by decide)
  have d24 : StackNames.findNameSpt stackConf.regNames 2 ≠
      StackNames.findNameSpt stackConf.regNames 4 :=
    fun e => absurd (hbij.1 e) (by decide)
  have d34 : StackNames.findNameSpt stackConf.regNames 3 ≠
      StackNames.findNameSpt stackConf.regNames 4 :=
    fun e => absurd (hbij.1 e) (by decide)
  simp only [s3, MakeInit.makeInit, HolFiniteMapExact.updateListEq, List.map_cons, List.map_nil,
    FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL, HolFiniteMapExact.empty]
  rcases hi with rfl | rfl | rfl <;> simp [d23, d24, d34]

theorem propagateThese_s2
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    StackRemove.Proofs.InitMake.propagateThese
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) bitmaps dataSp := by
  obtain ⟨gd, -, -, -, hmem, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbij⟩ := id hA
  obtain ⟨ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cb, le, a2, a4, abp, big, sep⟩ :=
    hmem
  obtain ⟨-, -, -, -, -, hm, hd, hcb, -⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset) (code := code)
    (t := t) (saveRegs := saveRegs) (coracle := coracle)
  refine ⟨gd, ptr2, ptr3, ptr4, bp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, a2, a4, abp, ?_, ?_⟩
  · rw [s2_regs_lookup hbij (.inl rfl), r2]
  · rw [s2_regs_lookup hbij (.inr (.inl rfl)), r3]
  · rw [s2_regs_lookup hbij (.inr (.inr rfl)), r4]
  · rw [hm]; exact m0
  · rw [hm]; exact m1
  · rw [hm, m2, BitVec.add_assoc, BitVec.add_comm (StackRemove.bytesInWord width * _),
      ← BitVec.add_assoc]
  · rw [hm, hcb]; exact m3
  · rw [hm, hcb]; exact m4
  · rw [hcb]; exact cb
  · exact BitVec.le_def.mp le
  · exact BitVec.le_def.mp big
  · rw [hm, hd]; exact sep

theorem sptAListLookup_mem {α : Type} {k : Nat} {v : α} :
    ∀ {l : List (Nat × α)}, sptAListLookup k l = some v → (k, v) ∈ l
  | [], h => by simp [sptAListLookup] at h
  | (k', v') :: es, h => by
      simp only [sptAListLookup] at h
      split at h
      · rename_i e; subst e; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sptAListLookup_mem h)

/-- The composed initialization semantics (Flapjack assembly of the four
`make_init_semantics` stages and rawcall's `compile_semantics`). -/
theorem assemble {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle) :
    opt ≠ none ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s ≠ .fail →
        Flapjack.Compiler.Backend.LabSem.semantics t =
          StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s) := by
  rw [fullMakeInit_eq] at hfm
  simp only [Prod.mk.injEq] at hfm
  obtain ⟨rfl, rfl⟩ := hfm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := id hA
  obtain ⟨s1, hopt, hsem⟩ := StackRemove.Proofs.InitSemantics.makeInitSemantics stackConf.jump
    offset (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (coracle1 coracle) (code1 dataConf code)
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) bitmaps dataSp
    ⟨dischargeThese_s2 hA, propagateThese_s2 hA⟩
  refine ⟨by rw [hopt]; simp, fun hS => ?_⟩
  have hs1 : StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap
      bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = s1 := by
    unfold StackRemove.Proofs.InitMake.makeInitAny
    rw [hopt]
  rw [hs1] at hS ⊢
  obtain ⟨post, hpost, hprop⟩ := StackRemove.Proofs.InitAny.makeInitOpt_eq_some hopt
  -- rawcall
  have hF := StackRawCall.CompileSemantics.compileSemantics code
    (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1) BvlToBvi.initGlobalsLocation
    hgood.1 (by simp [StackAlloc.makeInit]) rfl hS
  have hm : { StackAlloc.makeInit dataConf (sptFromAList code) coracle s1 with
      code := sptFromAList (StackRawCall.compile code) } =
      StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1 := by
    simp [StackAlloc.makeInit]
  rw [hm] at hF
  -- stack_alloc
  have hu := StackRemove.Proofs.InitAny.makeInitAnyUseStack (StackToLab.isGenGc dataConf.gcKind)
    maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
    (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
  have hus := StackRemove.Proofs.InitAny.makeInitAnyUseStore (StackToLab.isGenGc dataConf.gcKind)
    maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
    (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
  have hua := StackRemove.Proofs.InitAny.makeInitAnyUseAlloc (StackToLab.isGenGc dataConf.gcKind)
    maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
    (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
  have hcd := StackRemove.Proofs.InitAny.makeInitAnyCode (StackToLab.isGenGc dataConf.gcKind)
    maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
    (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
  have hco := StackRemove.Proofs.InitAny.makeInitAnyCompileOracle
    (StackToLab.isGenGc dataConf.gcKind)
    maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
    (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
  rw [hs1] at hu hus hua hcd hco
  have hE := StackAlloc.make_init_semantics (code := StackRawCall.compile code) (oracle := coracle)
    (s := s1) (c := dataConf) (start := BvlToBvi.initGlobalsLocation) ⟨?_, ?_, hu, hus,
      by simp [hua], hcd, hco, ?_, ?_, by rw [StackRawCall.mapFstCompile]; exact hgood.1,
      by rw [hF]; exact hS⟩
  · have h1 := hE.trans hF
    have hS1 : StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1 ≠ .fail := by
      rw [h1]; exact hS
    have hD := hsem hS1
    rw [← h1, ← hD]
    exact stageLab hA (by rw [hD]; exact hS1)
  · intro k prog hk
    obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hst, hal⟩ := hgood.2.1 _ hm0
    refine ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega,
      (StackRawCall.callArgComp _ _).2.mpr hal⟩
  · intro i k q hq
    obtain ⟨hst, hal⟩ := (hgoodO i).2.1 _ hq
    exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega, hal⟩
  · subst hpost
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hdb, _, _, _, hbl, _⟩
    simp only [StackRemove.Proofs.InitReduce.initReduce] at hbl hdb ⊢
    simp only [List.length_nil, Nat.add_zero]
    omega
  · subst hpost
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, hsb, _⟩
    exact hsb

end Stage

/-- HOL `full_make_init_semantics` (line 3365): from the full initialization of a
LabSem state satisfying the memory, register and code assumptions, the optional
stack_remove initialization succeeds and the LabSem semantics of the compiled
code is the non-failing StackSem semantics of the source from
`InitGlobals_location`. `markerTheory.Abbrev` around the conclusion is the
identity; `BIJ f UNIV UNIV` is `Function.Bijective f`; HOL sets are Bool
predicates; `EVERY P [2;3;4]` is a membership quantifier; the `let (c,p,b)` of
the oracle equation is rendered by projections. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_semantics" 3365
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem fullMakeInitSemantics {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {opt : Option (StackSemStateFiniteExact width C F)} :
    fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle =
      (s, opt) ∧
    goodDimindex width ∧
    t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
    t.compileOracle = (fun n => ((coracle n).1,
      StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp (coracle n).2.1)) ∧
    ¬t.failed = true ∧
    MakeInit.memoryAssumption stackConf.regNames bitmaps dataSp t ∧
    StackRemove.maxStackAlloc ≤ maxHeap ∧
    ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
    (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
    (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
    (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
    (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
    GoodCode.goodCode sp code ∧
    (∀ n, GoodCode.goodCode sp (coracle n).2.1) ∧
    10 ≤ sp ∧
    (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
    StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
    StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
    StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
    StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
    StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
    Function.Bijective (StackNames.findNameSpt stackConf.regNames) →
    opt ≠ none ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s ≠ .fail →
        Flapjack.Compiler.Backend.LabSem.semantics t =
          StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s) :=
  fun ⟨hfm, hA⟩ => assemble hfm hA

/-- HOL `full_make_init_semantics` rebound at line 3617 with `Abbrev`
rewritten away: the same statement. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_semantics" 3617
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem fullMakeInitSemantics' {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {opt : Option (StackSemStateFiniteExact width C F)} :
    fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle =
      (s, opt) ∧
    goodDimindex width ∧
    t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
    t.compileOracle = (fun n => ((coracle n).1,
      StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp (coracle n).2.1)) ∧
    ¬t.failed = true ∧
    MakeInit.memoryAssumption stackConf.regNames bitmaps dataSp t ∧
    StackRemove.maxStackAlloc ≤ maxHeap ∧
    ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
    (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
    (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
    (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
    (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
    GoodCode.goodCode sp code ∧
    (∀ n, GoodCode.goodCode sp (coracle n).2.1) ∧
    10 ≤ sp ∧
    (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
    StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
    StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
    StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
    StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
    StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
    Function.Bijective (StackNames.findNameSpt stackConf.regNames) →
    opt ≠ none ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s ≠ .fail →
        Flapjack.Compiler.Backend.LabSem.semantics t =
          StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s) :=
  fun ⟨hfm, hA⟩ => assemble hfm hA

end Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
