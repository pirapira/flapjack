import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.LabProps.SectionEnd
import Flapjack.Compiler.Backend.WordGcFunctions.HasFpOps
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Assembly
import Flapjack.Compiler.Backend.StackRemove.Proofs.AsmName
import Flapjack.Compiler.Backend.StackRawCall.Proofs.AsmNames
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Conventions
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InitStoreOk
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunOk
import Flapjack.Compiler.Backend.WordToStack.Proofs.InitializationStateRel

/-! The encoding and initial-state group of `stack_to_labProofScript.sml:3620-3799`.
`flatten_line_ok_pre` and `compile_all_enc_ok_pre` live in
`StackToLab/Proofs/Encoding`; this module holds the remaining declarations of
the group. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Pancake

/-- HOL `EVERY_sec_ends_with_label_MAP_prog_to_section`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "EVERY_sec_ends_with_label_MAP_prog_to_section" (words_as_type_indexed_bitvec)]
theorem everySecEndsWithLabelMapProgToSection {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width),
      ∀ sec ∈ prog.map progToSectionHOL, LabProps.secEndsWithLabelNative sec := by
  intro prog sec hsec
  obtain ⟨⟨n, p⟩, _, rfl⟩ := List.mem_map.mp hsec
  rw [progToSection_eq]
  simp [LabProps.secEndsWithLabelNative, LabSem.isLabelHOL]

/-- HOL `full_make_init_has_fp_ops`: the floating-point flags of the data
configuration do not affect `full_make_init`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem fullMakeInitHasFpOps {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dconf : DataToWord.Config} {b1 b2 : Bool} {mheap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {s : LabSem.State width C F} {saveRegs : Nat → Bool}
    {dsp : Nat} {cor : Nat → C × List (Nat × HolProg width) × List (BitVec width)} :
    fullMakeInit stackConf { dconf with hasFpOps := b1, hasFpTern := b2 } mheap sp offset bitmaps
        code s saveRegs dsp cor =
      fullMakeInit stackConf dconf mheap sp offset bitmaps code s saveRegs dsp cor := by
  unfold fullMakeInit StackAlloc.makeInit
  rw [WordGcFunctions.wordGcFun_hasFpOps]
  rfl

/-- HOL `stack_to_lab_compile_all_enc_ok`. HOL's free `c c1 c2 c3 sp prog`
are implicit; all twenty premises are kept in order. `names_ok`, `fixed_names`,
`conf_ok (:'a)`, `addr_offset_ok`/`byte_offset_ok c 0w` and `all_enc_ok_pre`
are the reviewed `namesOkSptHOL`, `fixedNames`, `confOk width`,
`asmAddrOffsetOkExact`/`asmByteOffsetOkExact c 0` and `allEncOkPreHOL`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_compile_all_enc_ok" (words_as_type_indexed_bitvec)]
theorem stackToLabCompileAllEncOk {width : Nat} [NeZero width] {c : AsmConfigExact width}
    {prog : List (Nat × HolProg width)} {c1 : StackToLab.Config} {c2 : DataToWord.Config}
    {c3 sp : Nat} :
    (∀ np ∈ prog, StackProps.stackAsmName c np.2) ∧
      (∀ np ∈ prog, StackProps.stackAsmRemove c np.2) ∧
      StackNames.namesOkSptHOL c1.regNames c.regCount c.avoidRegs ∧
      StackProps.fixedNames c1.regNames c ∧
      asmAddrOffsetOkExact c 0 = true ∧ goodDimindex width ∧ asmByteOffsetOkExact c 0 = true ∧
      (∀ n, n ≤ StackRemove.maxStackAlloc →
        c.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
        c.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true) ∧
      c.validImm (.inl .add) 1 = true ∧ c.validImm (.inl .sub) 1 = true ∧
      c.validImm (.inl .add) 4 = true ∧ c.validImm (.inl .add) 8 = true ∧
      (∀ s, asmAddrOffsetOkExact c (StackRemove.storeOffset s) = true) ∧
      StackProps.regName 10 c ∧ StackProps.regName (sp + 2) c ∧ StackProps.regName (sp + 1) c ∧
      StackProps.regName sp c ∧ DataToWord.confOk width c2 ∧ sp ≠ 0 →
      LabProps.allEncOkPreHOL c (StackToLab.compile c1 c2 c3 sp c.addrOffset prog) := by
  rintro ⟨hn, hr, hno, hfix, h0, hdim, hb0, himm, ha1, hs1, h4, h8, hst, h10, hk2, hk1, hk,
    hconf, hk0⟩
  have hraw := StackRawCall.stackAllocStackAsmConvs (c := c) (prog := prog)
  have halloc := StackAlloc.stack_alloc_stack_asm_convs (conf := c2)
    ⟨hraw.1 ▸ hn, hraw.2 ▸ hr, hconf, h0, h10, hdim, h8, h4, ha1, hs1⟩
  have hremove := StackRemove.Proofs.AsmName.stackRemoveStackAsmName (jump := c1.jump)
    (genGc := StackToLab.isGenGc c2.gcKind) (maxHeap := c3) (start := BvlToBvi.initGlobalsLocation)
    ⟨halloc.1, halloc.2, h0, hdim, himm, h4, h8, hst,
      StackRemove.Proofs.AsmName.regName_of_le h10 (by omega), hk2, hk1, hk, hk0⟩
  exact compileAllEncOkPreHOL c _ hb0 (StackNames.stackNamesStackAsmOk c c1.regNames _
    ⟨hremove, hno, hfix⟩)

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- `make_init_opt` returns only states satisfying `init_prop` (Flapjack
infrastructure: the `if` of `make_init_opt_def`). -/
theorem initProp_of_makeInitOpt {width : Nat} [NeZero width] {C F : Type} {gen : Bool}
    {maxHeap : Nat} {bitmaps : List (BitVec width)} {dataSp : Nat}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat} {code : Spt (HolProg width)}
    {s t : StackSemStateFiniteExact width C F}
    (h : StackRemove.Proofs.InitMake.makeInitOpt gen maxHeap bitmaps dataSp oracle jump bounds
      pointer code s = some t) :
    StackRemove.Proofs.InitProp.initProp gen maxHeap dataSp
      (StackRemove.Proofs.InitLimits.getStackHeapLimit maxHeap
        (StackRemove.Proofs.InitLimits.readPointers s)) t := by
  unfold StackRemove.Proofs.InitMake.makeInitOpt at h
  split at h
  · simp at h
  · split at h
    · cases h; assumption
    · simp at h

/-- HOL `IMP_init_store_ok`. HOL's free `stack_conf c1 sp offset bitmaps code s
save_regs data_sp coracle fmis xxx` are implicit; `fmis.store \\ Handler` is
`fmis.store.eraseEq .handler`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IMP_init_store_ok"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem impInitStoreOk {width : Nat} [NeZero width] {C F : Type} {maxHeap : Nat}
    {c1 : DataToWord.Config} {stackConf : StackToLab.Config} {sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {s : LabSem.State width C F} {saveRegs : Nat → Bool}
    {dataSp : Nat} {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {fmis : StackSemStateFiniteExact width C F} {xxx : Option (StackSemStateFiniteExact width C F)} :
    maxHeap = 2 * DataToWord.maxHeapLimit width c1 - 1 ∧
      (fmis, xxx) = fullMakeInit stackConf c1 maxHeap sp offset bitmaps code s saveRegs dataSp
        coracle →
      DataToWord.Proofs.Gc.initStoreOk c1 (fmis.store.eraseEq .handler) fmis.memory fmis.mdomain
        fmis.codeBuffer fmis.dataBuffer := by
  rintro ⟨hmh, hf⟩
  simp only [fullMakeInit, Prod.mk.injEq] at hf
  obtain ⟨rfl, -⟩ := hf
  simp only [StackAlloc.makeInit]
  unfold StackRemove.Proofs.InitMake.makeInitAny
  split
  · rename_i t ht
    obtain ⟨cur, oth, bb, len, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ :=
      initProp_of_makeInitOpt ht
    have hmem : Misc.wordListExists cur (len + len)
        (SetSep.fun2Set (t.memory, fun a => t.mdomain a = true)) := by
      rw [StackRemove.Proofs.WordListMemory.wordListExistsAdd, ← h26]
      exact h32
    refine ⟨len, cur, by omega, ?_⟩
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, reduceCtorEq, if_false]
    refine ⟨h10, h11, h13, h1, by rw [h5, h4], h2, by rw [h4, h26]; rfl, ?_,
      by rw [h7, BitVec.mul_comm]; rfl, h14, h15, h16, h17, h19, h20, hmem, h27⟩
    rw [h3]
    rcases c1.gcKind <;> simp [StackToLab.isGenGc, h26] <;> rfl
  · refine ⟨0, 0, Nat.zero_le _, ?_⟩
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, reduceCtorEq, if_false,
      HolFiniteMapExact.lookup_updateListEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial, ?_, ?_⟩
    all_goals try (simp [FUPDATE_LIST_HOL, FUPDATE_HOL, StackRemove.storeList,
      StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.empty]; done)
    · rcases c1.gcKind <;> simp [FUPDATE_LIST_HOL, FUPDATE_HOL, StackRemove.storeList,
        StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.empty]
    · have key : ∀ heap : (BitVec width × WordLocW width) → Prop, heap = (fun _ => False) →
          Misc.wordListExists 0 (0 + 0) heap := by
        rintro _ rfl
        refine ⟨[], fun _ => False, fun _ => False, ⟨?_, by simp⟩, rfl, rfl, rfl⟩
        funext e; simp
      exact key _ (by funext e; simp [SetSep.fun2Set])
    · have h0 : holAlign (holLOG2 (width / 8)) (0 : BitVec width) = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i _
        simp [holAlign, holWordSlice, getLsbD_holFcpWord]
      simp only [holByteAligned, holAligned, decide_eq_true_eq]
      exact h0

/-- `make_init_opt` returns an `init_reduce` state (Flapjack infrastructure). -/
theorem initReduce_of_makeInitOpt {width : Nat} [NeZero width] {C F : Type} {gen : Bool}
    {maxHeap : Nat} {bitmaps : List (BitVec width)} {dataSp : Nat}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat} {code : Spt (HolProg width)}
    {s t : StackSemStateFiniteExact width C F}
    (h : StackRemove.Proofs.InitMake.makeInitOpt gen maxHeap bitmaps dataSp oracle jump bounds
      pointer code s = some t) :
    ∃ t', t = StackRemove.Proofs.InitReduce.initReduce gen jump bounds pointer code bitmaps
      dataSp oracle t' := by
  unfold StackRemove.Proofs.InitMake.makeInitOpt at h
  split at h
  · simp at h
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · simp at h

theorem drop_eq_singleton_of_holLast {α : Type} [Nonempty α] :
    ∀ (l : List α) (n : Nat) (x : α), l.length = n + 1 → holLast l = x → l.drop n = [x]
  | [], _, _, h, _ => by simp at h
  | [a], n, x, h, hl => by
      simp at h; subst h; simpa [holLast] using hl
  | a :: b :: l, 0, x, h, _ => by simp at h
  | a :: b :: l, n + 1, x, h, hl => by
      simp only [List.drop_succ_cons]
      exact drop_eq_singleton_of_holLast (b :: l) n x (by simpa using h) (by simpa [holLast] using hl)

/-- HOL `IMP_init_state_ok`. HOL's free variables are implicit; `EVERY P progs`
over the Boolean conventions is `progs.all P = true`, as in the reviewed
`init_state_ok`, and `(λy. raise_stub_location ≠ y) ∘ FST` keeps HOL's
orientation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IMP_init_state_ok"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem impInitStateOk {width : Nat} [NeZero width] {C F : Type} {kkk : Nat}
    {bitmaps t : List (BitVec width)}
    {wordOracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    {stackOracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {ac : AsmConfigExact width} {scc : StackToLab.Config} {dc : DataToWord.Config}
    {maxHeap stk : Nat} {stoff : BitVec width × BitVec width} {p6 : List (Nat × HolProg width)}
    {labSt : LabSem.State width C F} {saveRegs : Nat → Bool} {dataSp : Nat}
    {fmis xxx : StackSemStateFiniteExact width C F} :
    4 < kkk ∧ bitmaps = 4 :: t ∧ goodDimindex width ∧
      (∀ n,
        let ((bm0, _), progs) := wordOracle n
        progs.all (fun p => postAllocConventionsHOL kkk p.2.2) = true ∧
        progs.all (fun p => flatExpConventions p.2.2) = true ∧
        progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
        progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
        (n = 0 → bm0 = bitmaps.length)) ∧
      stackOracle = (fun n =>
        let ((bm0, cfg), progs) := wordOracle n
        let (progs, _, bm) := compileWordToStackNative ac false kkk progs (.nil, bm0)
        (cfg, progs, appListAppend bm.1)) ∧
      fullMakeInit scc dc maxHeap stk stoff bitmaps p6 labSt saveRegs dataSp stackOracle =
        (fmis, some xxx) →
      WordToStackProofs.InitializationStateRel.initStateOk ac kkk fmis wordOracle := by
  rintro ⟨hk, rfl, hdim, hconv, horacle, hf⟩
  simp only [fullMakeInit, Prod.mk.injEq] at hf
  obtain ⟨hfmis, hopt⟩ := hf
  subst hfmis
  unfold StackRemove.Proofs.InitMake.makeInitAny
  rw [hopt]
  obtain ⟨cur, oth, bb, len, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ :=
    initProp_of_makeInitOpt hopt
  obtain ⟨t', rfl⟩ := initReduce_of_makeInitOpt hopt
  simp only [StackAlloc.makeInit, WordToStackProofs.InitializationStateRel.initStateOk]
  refine ⟨hk, hdim, by rcases hdim with h | h <;> omega, trivial, h22, trivial,
    DataToWord.Proofs.Gc.gcFunOkWordGcFun, by omega, h23, ?_, ?_,
    h25, drop_eq_singleton_of_holLast _ _ _ h29 h28, Option.ne_none_iff_exists'.mpr ⟨_, h12⟩,
    ?_, horacle, ?_⟩
  all_goals simp only [StackRemove.Proofs.InitReduce.initReduce] at h24 ⊢
  · simp at h24 ⊢; omega
  · exact ⟨t, rfl⟩
  · simp at h24 ⊢; omega
  · intro n
    simpa [ne_comm] using hconv n

end Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
