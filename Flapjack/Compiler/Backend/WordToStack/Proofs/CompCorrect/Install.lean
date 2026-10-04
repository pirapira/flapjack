import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocStateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionPrefix
import Flapjack.Misc.Sptree.Wf
import Flapjack.Misc.Sptree.ToAList

/-!
# Word-to-Stack `comp_correct`: the `Install` case

`word_to_stackProofScript.sml:6943-7070`. The code pointer and length sit in
source variables 2 and 4 (target registers 1 and 2); the data pointer and
length are loaded by `wReg1`/`wReg2`. The installed programs are compiled by
`compile_word_to_stack` on the target side, so the target oracle, bitmaps and
code table stay related; the cut environment keeps only stack-placed names, so
the registers the target discards are unobservable.
-/

namespace Flapjack.WordToStackProofs.CompCorrect.Install
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- The post-allocation conventions of an `Install` fix its code pointer and
length registers, keep its data registers physical, and place every cutset
name on the stack. Flapjack helper; no separate HOL original. -/
theorem installConventions {width : Nat} [NeZero width] (k : Nat)
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (h : postAllocConventionsHOL k
      ((.install ptr len dptr dlen names) : WordLangProgHOL (BitVec width)) = true) :
    ptr = 2 ∧ len = 4 ∧ dptr % 2 = 0 ∧ dlen % 2 = 0 ∧
      (∀ x, sptDomain names.1 x → x % 2 = 0 ∧ 2 * k ≤ x) ∧
      (∀ x, sptDomain names.2 x → x % 2 = 0 ∧ 2 * k ≤ x) := by
  simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL,
    everyNameHOL, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hd⟩, hl⟩, hv1, hv2⟩, ⟨hs1, hs2⟩, h1, h2⟩ := h
  have key : ∀ (t : Spt Unit) x, sptDomain t x → x ∈ (sptToAList t).map Prod.fst := by
    intro t x hx
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
    exact List.mem_map.mpr ⟨(x, u), (sptToAList_mem_iff_lookup t x u).mpr hu, rfl⟩
  refine ⟨h1, h2, by simpa [isPhyVar] using hd, by simpa [isPhyVar] using hl,
    fun x hx => ⟨?_, hs1 x (key _ x hx)⟩, fun x hx => ⟨?_, hs2 x (key _ x hx)⟩⟩
  · have := hv1 x (key _ x hx); simpa [isPhyVar] using this
  · have := hv2 x (key _ x hx); simpa [isPhyVar] using this

/-- HOL `ALOOKUP` agrees with the first-match lookup behind `fromAList`.
Flapjack infrastructure; no separate HOL original. -/
theorem sptAListLookup_eq_panPropsALookupEq {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq_panPropsALookupEq key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

/-- A successful `ALOOKUP` names a member of the list. Flapjack infrastructure. -/
theorem mem_of_panPropsALookupEq {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho; simp at h; subst h; exact List.mem_cons_self
      · simp [ho] at h
        exact List.mem_cons_of_mem _ (mem_of_panPropsALookupEq h)

/-- The post-`Install` states remain related (the state-relation part of the
HOL case, `word_to_stackProofScript.sml:6987-7069`). Flapjack factoring of the
original proof; there is no separate HOL declaration. -/
theorem installRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat)
    (related : stateRel ac k f frame source t lens 0)
    (names : WordLangCutsetsHOL)
    (hc1 : ∀ x, sptDomain names.1 x → x % 2 = 0 ∧ 2 * k ≤ x)
    (hc2 : ∀ x, sptDomain names.2 x → x % 2 = 0 ∧ 2 * k ≤ x)
    (env : Spt (WordLocW width)) (hce : wordSemCutEnv names source.locals = some env)
    (bm0 : Nat) (cfg : C) (kk argc : Nat) (prog : WordLangProgHOL (BitVec width))
    (rest : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hor : source.compileOracle 0 = ((bm0, cfg), (kk, argc, prog) :: rest))
    (progs2 : List (Nat × HolProg width)) (fs : List Nat) (bm : AppList (BitVec width) × Nat)
    (hcw : compileWordToStackNative ac false k ((kk, argc, prog) :: rest) (.nil, bm0) =
      (progs2, fs, bm))
    (cfg2 : C) (hcfg : (source.compileOracle 1).1 = (bm.2, cfg2))
    (cb : WordSemBuffer width 8) (db : WordSemBuffer width width)
    (hdata : source.dataBuffer.buffer = appListAppend bm.1)
    (hdb : db.buffer = [] ∧ db.spaceLeft = source.dataBuffer.spaceLeft) :
    stateRel ac k f frame
      { source with
        codeBuffer := cb
        dataBuffer := db
        code := sptUnion source.code (sptFromAList ((kk, argc, prog) :: rest))
        locals := sptInsert 2 (.loc kk 0) env
        fpRegs := HolFiniteMapExact.empty
        compileOracle := holShiftSeq 1 source.compileOracle
        stackMax := none
        stackSize := .ln }
      { t with
        bitmaps := t.bitmaps ++ appListAppend bm.1
        codeBuffer := cb
        dataBuffer := db
        code := sptUnion t.code (sptFromAList progs2)
        regs := (StackSemStateOps.restrictIn t.regs t.ffiSaveRegs).updateEq (1, .loc kk 0)
        fpRegs := HolFiniteMapExact.empty
        compileOracle := holShiftSeq 1 t.compileOracle } lens 0 := by
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := related'
  -- Facts about the compiled installed programs.
  have hmap := mapFstCompileWordToStack ac false k _ _ _ _ hcw
  have hlen := compileWordToStackImpLength ac false k _ .nil bm0 progs2 fs bm.1 bm.2
    ⟨hcw, by simp [appListAppend, appendAux]⟩
  have h0 := r23 0
  simp only [hor] at h0
  obtain ⟨cv1, cv2, cv3, cv4, hbm0''⟩ := h0
  have hbm0' : bm0 = t.bitmaps.length := hbm0'' trivial
  simp only [appListAppend, appendAux, List.length_nil, Nat.sub_zero] at hlen
  have henv : env = sptUnion (sptInter source.locals names.2) (sptInter source.locals names.1) := by
    unfold wordSemCutEnv at hce
    rcases hcs : wordSemCutEnvs names source.locals with _ | ⟨e1, e2⟩
    · rw [hcs] at hce; cases hce
    rw [hcs] at hce
    obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcs
    simp only [Option.some.injEq] at hce he1 he2
    rw [← hce, ← he1, ← he2]
  unfold stateRel
  refine ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, rfl,
    rfl, rfl, r21, ?c22, ?c23, ?c24, ?c25, ?c26, ?c27, r28, r29, ?c30, ?c31, ?c32, r33, r34,
    r35, ?c36, ?c37, ?c38, ?cloc⟩
  case c22 =>
    funext n
    exact congrFun r22 (n + 1)
  case c23 =>
    intro n
    have h := r23 (n + 1)
    show (let ((bm0, _), progs) := source.compileOracle (n + 1)
      progs.all (fun p => postAllocConventionsHOL k p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (p.1 ≠ raiseStubLocation)) = true ∧
      progs.all (fun p => decide (p.1 ≠ storeConstsStubLocation)) = true ∧
      (n = 0 → bm0 = (t.bitmaps ++ appListAppend bm.1).length))
    rcases hso : source.compileOracle (n + 1) with ⟨⟨b1, c1⟩, ps⟩
    simp only [hso] at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hn => ?_⟩
    subst hn
    rw [hso] at hcfg
    simp only [Prod.mk.injEq] at hcfg
    rw [List.length_append, hcfg.1]
    simp only [appListAppend]
    omega
  case c24 =>
    rw [sptDomain_sptUnion, sptDomain_sptUnion, sptDomainFromAList,
      sptDomainFromAList, r24]
    funext x
    rw [hmap]
    apply propext
    tauto
  case c25 =>
    intro n wordProg argumentCount hlook
    change sptLookup n (sptUnion source.code (sptFromAList ((kk, argc, prog) :: rest))) =
      some (argumentCount, wordProg) at hlook
    rw [sptLookup_sptUnion] at hlook
    rcases hs : sptLookup n source.code with _ | v
    · rw [hs] at hlook
      simp only at hlook
      rw [sptLookup_sptFromAList, sptAListLookup_eq_panPropsALookupEq] at hlook
      have hmem := mem_of_panPropsALookupEq hlook
      simp only [List.all_eq_true, decide_eq_true_eq] at cv1 cv2 cv3 cv4
      have hn1 := cv3 _ hmem
      have hn2 := cv4 _ hmem
      obtain ⟨start, startIndex, finish, finishIndex, frame', body, hcomp, b1, b2, pre, hbody⟩ :=
        compileWordToStackImpALookup ac false k _ .nil bm0 progs2 fs bm.1 bm.2
          n argumentCount wordProg (t.bitmaps ++ appListAppend bm.1) hcw hlook
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux]; omega)
          (by simp [appListAppend, appendAux, hbm0'])
      refine ⟨cv1 _ hmem, cv2 _ hmem, start, startIndex, finish, finishIndex, frame', body,
        hcomp, b1, b2, pre, ?_, by simp⟩
      have htn : sptLookup n t.code = none := by
        have hd := congrFun r24 n
        have : ¬ sptDomain t.code n := by
          rw [hd]
          simp only [sptDomain, hs, Option.isSome_none, Bool.false_eq_true, or_false]
          omega
        simpa [sptDomain] using this
      change sptLookup n (sptUnion t.code (sptFromAList progs2)) = some body
      rw [sptLookup_sptUnion, htn]
      simp only
      rw [sptLookup_sptFromAList, sptAListLookup_eq_panPropsALookupEq]
      exact hbody
    · rw [hs] at hlook
      simp only [Option.some.injEq] at hlook
      subst hlook
      obtain ⟨c1, c2, bs, i, bs2, i2, fr, sp, hcomp, b1, b2, pre, hl, -⟩ := r25 n wordProg argumentCount hs
      refine ⟨c1, c2, bs, i, bs2, i2, fr, sp, hcomp, b1, by simp; omega, ?_, ?_, by simp⟩
      · rw [List.drop_append_of_le_length b2]
        exact pre.trans (List.prefix_append _ _)
      · change sptLookup n (sptUnion t.code (sptFromAList progs2)) = some sp
        rw [sptLookup_sptUnion, hl]
  case c26 =>
    change sptLookup raiseStubLocation (sptUnion t.code (sptFromAList progs2)) = _
    rw [sptLookup_sptUnion, r26]
  case c27 =>
    change sptLookup storeConstsStubLocation (sptUnion t.code (sptFromAList progs2)) = _
    rw [sptLookup_sptUnion, r27]
  case c30 =>
    show (t.bitmaps ++ appListAppend bm.1).length + db.buffer.length + db.spaceLeft + 1 < 2 ^ width
    rw [hdb.1, hdb.2, List.length_append, ← hdata]
    simpa using r30
  case c31 =>
    show 1 ≤ (t.bitmaps ++ appListAppend bm.1).length
    simp; omega
  case c32 =>
    show Flapjack.holHd (t.bitmaps ++ appListAppend bm.1) = (4 : BitVec width)
    rcases hb : t.bitmaps with _ | ⟨a, l⟩
    · rw [hb] at r31; simp at r31
    · rw [hb] at r32; simpa [Flapjack.holHd] using r32
  case c36 =>
    show sptWf (sptInsert 2 (.loc kk 0) env) = true
    apply sptWfInsert
    rw [henv]
    exact sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩
  case c37 =>
    obtain ⟨a, b, -⟩ := r37
    exact ⟨a, b, by simp⟩
  case c38 =>
    obtain ⟨hs, st, habs, hh, haux⟩ := r38
    exact ⟨hs, st, absStackBitmapsPrefix _ _ _ _ _ _ habs, hh, haux⟩
  case cloc =>
    intro m v hm
    change sptLookup m (sptInsert 2 (.loc kk 0) env) = some v at hm
    by_cases hm2 : m = 2
    · subst hm2
      rw [sptLookup_sptInsert_same] at hm
      cases hm
      refine ⟨rfl, ?_⟩
      rw [if_pos (by omega)]
      simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · rw [sptLookup_sptInsert_ne _ _ _ _ hm2] at hm
      rw [henv, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at hm
      have hlook : sptLookup m source.locals = some v ∧
          (sptDomain names.1 m ∨ sptDomain names.2 m) := by
        unfold sptDomain
        revert hm
        cases sptLookup m source.locals <;> cases sptLookup m names.2 <;>
          cases sptLookup m names.1 <;> simp
      obtain ⟨hl, hd⟩ := hlook
      have hev : m % 2 = 0 ∧ 2 * k ≤ m := hd.elim (hc1 m) (hc2 m)
      obtain ⟨he, hif⟩ := rloc m v hl
      refine ⟨he, ?_⟩
      rw [if_neg (by omega)] at hif ⊢
      exact hif

/-- Full original comp_correct Install case (`word_to_stackProofScript.sml:6943-7070`).
All original premises and the complete target clock/run/result/resource
conclusion are retained; the target run, the oracle/compiler agreement on the
installed programs and the post-state relation are derived. Evaluator closure
inherits reals_as_rational_cuts; no numerical FP assertion. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.install ptr len dptr dlen names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, hd3, hd4, hc1, hc2⟩ :=
    installConventions k ptr len dptr dlen names conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 dptr (k, f, frame) with ⟨xs, reg3⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 dlen (k, f, frame) with ⟨ys, reg4⟩
  have programEq := congrArg Prod.fst compilation
  simp only [compNative, fmt1, fmt2] at programEq
  subst compiled
  -- The source run.
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w1 | ⟨_, _⟩) <;>
    rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h3 : WordSemStateFiniteExact.getVar dptr source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h5 : WordSemStateFiniteExact.getVar dlen source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h2, h4, h3, h5, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hor : source.compileOracle 0 with ⟨⟨bm0, cfg⟩, progs⟩
  simp only [hor] at execution
  rcases hcf : wordSemBufferFlush source.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
    rcases hdf : wordSemBufferFlush source.dataBuffer w3 w4 with _ | ⟨data, db⟩ <;>
    simp only [hcf, hdf, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hsc : source.compile (bm0, cfg) progs with _ | ⟨bytes', data', cfg'⟩ <;>
    rcases progs with _ | ⟨⟨kk, argc, prog⟩, rest⟩ <;>
    simp only [hsc, Prod.mk.injEq] at execution <;>
    try first
      | exact absurd execution.1.symm notError
      | exact absurd (congrArg Prod.fst execution).symm notError
  by_cases hcond : bytes = bytes' ∧ data = data' ∧
      (holShiftSeq 1 source.compileOracle 0).1 = cfg'
  swap
  · rw [if_neg hcond] at execution
    exact absurd (congrArg Prod.fst execution).symm notError
  rw [if_pos hcond] at execution
  simp only [Prod.mk.injEq] at execution
  obtain ⟨rfl, rfl⟩ := execution
  -- The target loads of the data pointer and length.
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame dptr reg3 xs source target lens
      (.word w3) fmt1 hd3 h3 related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame dlen reg4 ys source t1 lens
      (.word w4) fmt2 hd4 h5 rel1
  have r10 : 4 < k := rel2.2.2.2.2.2.2.2.2.2.1
  have read1 : StackSemStateOps.getVar 1 t2 = some (.word w1) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 2 _
      ⟨rel2, h2, rfl, by omega⟩
    simpa using this
  have read2 : StackSemStateOps.getVar 2 t2 = some (.word w2) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 4 _
      ⟨rel2, h4, rfl, by omega⟩
    simpa using this
  have read3 : StackSemStateOps.getVar reg3 t2 = some (.word w3) := by
    rw [otherReads reg3 regNe]; exact loaded1
  -- The target compiler and oracle on the installed programs.
  have rel2' := rel2
  unfold stateRel at rel2'
  obtain ⟨-, -, -, -, r5, -, -, -, -, -, -, -, -, -, -, -, -, -, r19, r20, r21, r22, -⟩ := rel2'
  rcases hcw : compileWordToStackNative ac false k ((kk, argc, prog) :: rest) (.nil, bm0) with
    ⟨progs2, fs, bm⟩
  have hsc' := hsc
  rw [r21] at hsc'
  simp only [hcw] at hsc'
  rcases htc : t2.compile cfg progs2 with _ | ⟨bytes2, cfg2⟩
  · simp [htc] at hsc'
  simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc'
  obtain ⟨rfl, rfl, rfl⟩ := hsc'
  have hor2 : t2.compileOracle 0 = (cfg, progs2, appListAppend bm.1) := by
    rw [r22]; simp only [hor, hcw]
  have hmap := mapFstCompileWordToStack ac false k _ _ _ _ hcw
  rcases progs2 with _ | ⟨⟨kk2, prog2⟩, rest2⟩
  · simp at hmap
  simp only [List.map_cons, List.cons.injEq] at hmap
  obtain ⟨rfl, -⟩ := hmap
  have hflush : wordSemBufferFlush source.dataBuffer w3 w4 = some (data, db) := hdf
  have hdata : source.dataBuffer.buffer = appListAppend bm.1 := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [hflush.1, hcond.2.1]
    · cases hflush
  have hdb : db.buffer = [] ∧ db.spaceLeft = source.dataBuffer.spaceLeft := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [← hflush.2]; exact ⟨rfl, rfl⟩
    · cases hflush
  have hcfg : (source.compileOracle 1).1 = (bm.2, cfg2) := hcond.2.2
  have hnew : (holShiftSeq 1 t2.compileOracle 0).1 = cfg2 := by
    show (t2.compileOracle 1).1 = cfg2
    rcases hso : source.compileOracle 1 with ⟨⟨b1, c1⟩, ps⟩
    rw [r22]
    simp only [hso]
    rw [hso] at hcfg
    simp only [Prod.mk.injEq] at hcfg
    rcases compileWordToStackNative ac false k ps (.nil, b1) with ⟨a, b, c⟩
    exact hcfg.2
  -- The target run and the related post-states.
  refine ⟨0, { t2 with
      bitmaps := t2.bitmaps ++ appListAppend bm.1
      codeBuffer := cb
      dataBuffer := db
      code := sptUnion t2.code (sptFromAList ((kk2, prog2) :: rest2))
      regs := (StackSemStateOps.restrictIn t2.regs t2.ffiSaveRegs).updateEq (1, .loc kk2 0)
      fpRegs := HolFiniteMapExact.empty
      compileOracle := holShiftSeq 1 t2.compileOracle }, none, ?_, ?_⟩
  · simp only [Nat.add_zero, wStackLoadAppend, Function.comp_apply,
      show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)), t1) =
        (none, t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)), t2) =
        (none, t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix2]
    rw [StackSemEvaluate.evaluate_install]
    simp only [read1, read2, read3, loaded2, hor2, r20, r19, r5, hcf, hflush, if_true, htc]
    rw [if_pos ⟨hcond.1, hcond.2.1.trans (congrArg (fun x => x.2.2) hor2).symm, hnew⟩]
  · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
    exact installRelation ac k f frame source t2 lens rel2 names hc1 hc2 env hce bm0 cfg kk2 argc
      prog rest hor (_ :: rest2) fs bm hcw cfg2 hcfg cb db hdata hdb

end Flapjack.WordToStackProofs.CompCorrect.Install
