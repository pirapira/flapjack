import Flapjack.Compiler.Backend.WordToWord.Proofs.Syntactic
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts

/-!
# `word_to_wordProof`: `no_install_no_alloc_compile_single_correct`

HOL proves `no_install_no_alloc_compile_single_correct`
(`word_to_wordProofScript.sml:1092-1690`) by the same complete induction as
`compile_single_correct`, case by case. Here it follows from the ported
`compile_single_correct`: a program without `Install`, run on a code table
without `Install`, never reads or changes the compile oracle or the `compile`
function (`evaluate_compileFields_frame`), so the two theorems' runs differ
only in those fields.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps Flapjack.Compiler.Encoders.Asm

section CompileFieldsFrame

variable {width : Nat} [NeZero width] {C F : Type}

/-- The state with the compile oracle and `compile` replaced (Flapjack infrastructure). -/
abbrev cfState (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (s : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { s with compileOracle := o, compile := cc }

variable (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
  (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
    Option (List (BitVec 8) × List (BitVec width) × C))

theorem cf_getVar (x : Nat) (s : WordSemStateFiniteExact width C F) :
    getVar x (cfState o cc s) = getVar x s := rfl

theorem cf_getVars (xs : List Nat) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVars xs (cfState o cc s) = WordSemStateFiniteExact.getVars xs s :=
  (getVars_congr (cfState o cc s) s rfl xs).symm

theorem cf_getVarImm (ri : WordRegImm (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVarImm ri (cfState o cc s) = WordSemStateFiniteExact.getVarImm ri s := by
  cases ri <;> rfl

theorem cf_pushEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    pushEnv envs h (cfState o cc s) = cfState o cc (pushEnv envs h s) := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> rfl

theorem cf_popEnv (s : WordSemStateFiniteExact width C F) :
    popEnv (cfState o cc s) = (popEnv s).map (cfState o cc) := by
  unfold popEnv
  dsimp only
  split <;> rfl

theorem cf_cutState (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    cutState names (cfState o cc s) = (cutState names s).map (cfState o cc) := by
  unfold cutState
  dsimp only
  cases wordSemCutEnv names s.locals <;> rfl

/-- A leaf statement that keeps the code table commutes with replacing the compile
    fields (`evaluate_tgt_frame` at the unchanged code table). -/
theorem leafFrame (s : WordSemStateFiniteExact width C F) (p : WordLangProgHOL (BitVec width))
    (hp : cscLeaf p = true) (hcode : (evaluate p s).2.code = s.code) :
    evaluate p (cfState o cc s) = ((evaluate p s).1, cfState o cc (evaluate p s).2) := by
  have h := evaluate_tgt_frame s.code o cc s (fun _ => rfl) p hp
  have e1 : tgtState s.code o cc s = cfState o cc s := rfl
  have e2 : tgtState s.code o cc (evaluate p s).2 = cfState o cc (evaluate p s).2 := by
    unfold tgtState
    rw [← hcode]
  rw [e1, e2] at h
  exact h

set_option linter.unusedSimpArgs false in
/-- A program without `Install`, run on a code table without `Install`, commutes
    with replacing the compile oracle and `compile` (Flapjack infrastructure; the
    recursion follows `code_evaluate` on HOL's termination measure). -/
theorem evaluate_compileFields_frame :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      noInstallSubprogsHOL p = true → noInstallCode s.code →
      evaluate p (cfState o cc s) = ((evaluate p s).1, cfState o cc (evaluate p s).2)
  | .tick, s, _, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      split <;> rfl
  | .mustTerminate q, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hni
      by_cases hz : s.termdep = 0
      · rw [ht, ht]
        simp only [hz, dite_true, if_true]
      · rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        have ih := evaluate_compileFields_frame q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hni hc
        rw [hq] at ih
        rw [evaluate_mustTerminate_run q s hz r s1 hq,
          evaluate_mustTerminate_run q (cfState o cc s) hz r (cfState o cc s1) ih]
        split <;> rfl
  | .seq c1 c2, s, hni, hc => by
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      have ih1 := evaluate_compileFields_frame c1 s hni.1 hc
      rw [h1] at ih1
      have hc1 := evaluate_clock c1 s r1 s1 h1
      have hcode : s1.code = s.code := by
        have := code_evaluate c1 s hni.1 hc
        rw [h1] at this
        exact this
      rw [evaluate_seq_run c1 c2 s r1 s1 h1,
        evaluate_seq_run c1 c2 (cfState o cc s) r1 (cfState o cc s1) ih1]
      by_cases hr : r1 = none
      · simp only [hr, if_true]
        exact evaluate_compileFields_frame c2 s1 hni.2 (hcode ▸ hc)
      · simp only [hr, if_false]
  | .ite cmp r1 ri c1 c2, s, hni, hc => by
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      have e1 := evaluate_compileFields_frame c1 s hni.1 hc
      have e2 := evaluate_compileFields_frame c2 s hni.2 hc
      rw [evaluate_ite_read, evaluate_ite_read, cf_getVar, cf_getVarImm]
      rcases getVar r1 s with _ | x <;> rcases WordSemStateFiniteExact.getVarImm ri s with _ | y <;>
        simp only
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;> first | rfl | exact e1 | exact e2
  | .loop names c exitNames, s, hni, hc => by
      have hni' := hni
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni'
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rcases hcs : cutState (names, .ln) s with _ | s'
      · rw [ht, ht, cf_cutState, hcs]
        rfl
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      have ih := evaluate_compileFields_frame c { s with locals := l } hni' hc
      rw [hb] at ih
      have hcl := evaluate_clock c _ rb s1 hb
      have hcode : s1.code = s.code := by
        have := code_evaluate c { s with locals := l } hni' hc
        rw [hb] at this
        exact this
      have hcs' : cutState (names, .ln) (cfState o cc s) = some (cfState o cc { s with locals := l }) := by
        rw [cf_cutState, hcs]
        rfl
      rw [evaluate_loop_run names exitNames c s _ hcs rb s1 hb,
        evaluate_loop_run names exitNames c (cfState o cc s) _ hcs' rb (cfState o cc s1) ih]
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, if_true]
          rfl
        · simp only [hz, if_false]
          have hcd : noInstallCode (decClock s1).code := hcode ▸ hc
          exact evaluate_compileFields_frame (.loop names c exitNames) (decClock s1) hni hcd
      · simp only [hcont, Bool.false_eq_true, if_false]
        by_cases hbr : rb = some (.break 0)
        · simp only [hbr, if_true, cf_cutState]
          rcases cutState (exitNames, .ln) s1 <;> rfl
        · simp only [hbr, if_false]
  | .call ret dest args handler, s, hni, hc => by
      rw [evaluate_call_eq, evaluate_call_eq, cf_getVars]
      rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
      · rfl
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · rfl
      simp only
      have hprog := noInstallFindCode s.code dest _ _ _ prog _ ⟨hc, hf⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => rfl
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, if_true]
            rfl
          simp only [hz, if_false]
          have ih := evaluate_compileFields_frame prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) hprog hc
          rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          simp only
          rw [show WordSemStateFiniteExact.callEnv args1 ss (decClock (cfState o cc s)) =
            cfState o cc (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) from rfl, ih]
          split <;> rfl
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · rfl
        simp only
        by_cases hz : s.clock = 0
        · simp only [hz, if_true, cf_pushEnv]
          rfl
        simp only [hz, if_false]
        have hpre : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code := by
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        have ih := evaluate_compileFields_frame prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (hpre ▸ hc)
        rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih
        have hcl := evaluate_clock prog _ rc s2 hcv
        have h2 : s2.code = s.code := by
          have := code_evaluate prog _ hprog (hpre ▸ hc)
          rw [hcv] at this
          exact this.trans hpre
        rw [show WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock (cfState o cc s))) =
          cfState o cc (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) by
            rw [show decClock (cfState o cc s) = cfState o cc (decClock s) from rfl, cf_pushEnv]; rfl,
          ih]
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · rfl
        · simp only
          by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]
          simp only [hx, if_false, cf_popEnv]
          rcases hp : popEnv s2 with _ | s1
          · rfl
          simp only [Option.map_some]
          have h3 : s1.code = s.code :=
            ((popEnvConst _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · have hcs1 : noInstallCode (setVars n ys s1).code := h3 ▸ hc
            exact evaluate_compileFields_frame retHandler (setVars n ys s1) (noInstall_call_ret hni) hcs1
          · rfl
        · cases handler with
          | none => rfl
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · rfl
            · split
              · have hcs2 : noInstallCode (setVar n' y s2).code := h2 ▸ hc
                exact evaluate_compileFields_frame hprog' (setVar n' y s2) (noInstall_call_handler hni) hcs2
              · rfl
        all_goals rfl
  | .install a b c d f, s, hni, _ => by
      simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni
  | .skip, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .move a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .inst a, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .assign a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .get a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .set a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .store a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .alloc a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .storeConsts a b c d f, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .raise a, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | WordLangProgHOL.return a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | WordLangProgHOL.break a, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | WordLangProgHOL.continue a, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .opCurrHeap a b c, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .locValue a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .codeBufferWrite a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .dataBufferWrite a b, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .ffi a b c d f g, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
  | .shareInst a b c, s, hni, _ => leafFrame o cc s _ rfl (code_evaluate_const s _ rfl hni)
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, WordSemStateFiniteExact.callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

/-- Without `Install`, a run keeps the compile oracle and `compile` (the frame at the
    state's own fields). -/
theorem evaluate_compileFields_const (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hni : noInstallSubprogsHOL p = true)
    (hc : noInstallCode s.code) :
    (evaluate p s).2.compileOracle = s.compileOracle ∧ (evaluate p s).2.compile = s.compile := by
  have h := evaluate_compileFields_frame s.compileOracle s.compile p s hni hc
  have e : cfState s.compileOracle s.compile s = s := rfl
  rw [e] at h
  have h2 := congrArg Prod.snd h
  constructor
  · exact (congrArg WordSemStateFiniteExact.compileOracle h2).trans rfl
  · exact (congrArg WordSemStateFiniteExact.compile h2).trans rfl

end CompileFieldsFrame

/-- A code table related by `code_rel` to one without `Install`, with the same
    domain, has no `Install` (Flapjack infrastructure; HOL's `code_rel_no_install`
    reasoning on whole tables). -/
theorem noInstallCode_of_codeRel {width : Nat} [NeZero width]
    (code l : Spt (Nat × WordLangProgHOL (BitVec width))) (hrel : codeRel code l)
    (hdom : sptDomain code = sptDomain l) (hc : noInstallCode code) : noInstallCode l := by
  intro k n p hk
  have hm : (sptLookup k code).isSome = true := by
    have := congrFun hdom k
    simp only [sptDomain] at this
    rw [this, hk]
    rfl
  rcases hv : sptLookup k code with _ | ⟨ar, e⟩
  · rw [hv] at hm
    cases hm
  obtain ⟨col, t, kk, a, c, h⟩ := hrel k _ hv
  rw [hk] at h
  have hp : p = (compileSingle t kk a c ((k, ar, e), col)).2.2 := congrArg (·.2) (Option.some.inj h)
  have he := hc k ar e hv
  rw [hp]
  rw [noInstallSubprogsHOL_eq_notCreated] at he ⊢
  exact WordConvs.compile_single_not_created_subprogs _ t kk a c ((k, ar, e), col) he

namespace NoInstallCompileSingleCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end NoInstallCompileSingleCarrier

open Classical in
/-- HOL `no_install_no_alloc_compile_single_correct` (`word_to_wordProofScript.sml:1092-1690`):
    without `Install` in the program or the code table, running on a `code_rel`-related
    code table with the same domain reproduces every non-error source run from some
    permutation oracle. `if res = SOME Error` is decided classically. Derived from
    `compile_single_correct` (at an arbitrary `compile_single` configuration, which
    `code_rel` leaves free) and the compile-fields frame; the `no_alloc` premises,
    which HOL's case proof uses, are not needed on this route. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "no_install_no_alloc_compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem no_install_no_alloc_compile_single_correct {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (l : Spt (Nat × WordLangProgHOL (BitVec width))),
      codeRel st.code l ∧ noInstallSubprogsHOL prog = true ∧ noAllocSubprogsHOL prog = true ∧
        noInstallCode st.code ∧ noAllocCode st.code ∧ sptDomain st.code = sptDomain l ∧
        Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
      ∃ perm' : Nat → Nat → Nat,
        let (res, rst) := evaluate prog { st with permute := perm' }
        if res = some .error then True
        else
          let (res1, rst1) := evaluate prog { st with code := l }
          res1 = res ∧ codeRel rst.code rst1.code ∧ sptDomain rst.code = sptDomain rst1.code ∧
            rst1 = { rst with code := rst1.code } := by
  rintro prog st l ⟨hrel, hni, -, hnic, -, hdom, hgc⟩
  let co : AsmConfigExact width := ⟨.riscv, fun _ => [], false, 0, none, [], 0, 0, false,
    fun _ _ => false, (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)⟩
  let cs := fun p : Nat × Nat × WordLangProgHOL (BitVec width) => compileSingle false 0 0 co (p, none)
  let cc0 : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun _ _ => none
  let C' : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun conf progs => cc0 conf (progs.map cs)
  let O2 := Prod.map id (List.map cs) ∘ st.compileOracle
  let st' := cfState st.compileOracle C' st
  obtain ⟨perm', H⟩ := compile_single_correct false 0 0 co prog st' l O2 cc0 ⟨hrel, hdom, rfl, rfl, hgc⟩
  refine ⟨perm', ?_⟩
  have hnil : noInstallCode l := noInstallCode_of_codeRel st.code l hrel hdom hnic
  rcases hS : evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  have hA := evaluate_compileFields_frame st.compileOracle C' prog { st with permute := perm' } hni hnic
  have hSc := evaluate_compileFields_const prog { st with permute := perm' } hni hnic
  rw [hS] at hA hSc
  change evaluate prog { st' with permute := perm' } = (res, cfState st.compileOracle C' rst) at hA
  rw [hA] at H
  dsimp only at H
  dsimp only
  by_cases herr : res = some .error
  · simp [herr]
  rw [if_neg herr] at H ⊢
  rcases hT : evaluate prog { st with code := l } with ⟨res1, rst1⟩
  have hB := evaluate_compileFields_frame O2 cc0 prog { st with code := l } hni hnil
  have hTc := evaluate_compileFields_const prog { st with code := l } hni hnil
  rw [hT] at hB hTc
  change evaluate prog { st' with code := l, compileOracle := O2, compile := cc0 } =
    (res1, cfState O2 cc0 rst1) at hB
  rw [hB] at H
  dsimp only at H
  dsimp only
  obtain ⟨hres, hcr, hd, heq⟩ := H
  refine ⟨hres, hcr, hd, ?_⟩
  obtain ⟨hTo, hTcc⟩ := hTc
  obtain ⟨hSo, hScc⟩ := hSc
  cases rst1
  cases rst
  simp only [cfState, WordSemStateFiniteExact.mk.injEq] at heq hTo hTcc hSo hScc ⊢
  simp_all

end Flapjack.Compiler.Backend.WordToWord
