import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Pancake.Proofs.PanToTarget.WordToWordNoInstall
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConstFull
import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanToWord.NoInstallCode

/-!
# `pan_to_targetProof`: panLang stack-size constancy group

`cakeml/pancake/proofs/pan_to_targetProofScript.sml` 1000-1166: instructions and
shared-memory instructions keep the stack size, limit and maximum, so a run of a
program without `Install` or `Alloc` keeps the stack size and limit, and a start
call of compiled Pancake code never runs out of space; and `option_lt_SOME`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Pancake.PanLang

namespace StackSizeConstCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StackSizeConstCarrier

/-- HOL `inst_stack_size_const_panLang` (`pan_to_targetProofScript.sml:1026-1039`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_size_const_panLang"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_stack_size_const_panLang {width : Nat} [NeZero width] {C F : Type} :
    ∀ (i : WordLangInst (BitVec width)) (s t : WordSemStateFiniteExact width C F),
      inst i s = some t → t.stackSize = s.stackSize :=
  fun i s t h => (instConstFull i s t h).2.2.2.2.2.2.2.2.2.2.2.2

/-- HOL `inst_stack_limit_const_panLang` (`pan_to_targetProofScript.sml:1041-1054`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_limit_const_panLang"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_stack_limit_const_panLang {width : Nat} [NeZero width] {C F : Type} :
    ∀ (i : WordLangInst (BitVec width)) (s t : WordSemStateFiniteExact width C F),
      inst i s = some t → t.stackLimit = s.stackLimit :=
  fun i s t h => (instConstFull i s t h).2.2.2.2.2.2.2.2.2.2.1

/-- HOL `inst_stack_max_const_panLang` (`pan_to_targetProofScript.sml:1056-1069`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_stack_max_const_panLang"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_stack_max_const_panLang {width : Nat} [NeZero width] {C F : Type} :
    ∀ (i : WordLangInst (BitVec width)) (s t : WordSemStateFiniteExact width C F),
      inst i s = some t → t.stackMax = s.stackMax :=
  fun i s t h => (instConstFull i s t h).2.2.2.2.2.2.2.2.2.2.2.1

/-- HOL `share_inst_modifies` (`pan_to_targetProofScript.sml:1071-1095`): a shared-memory
    instruction changes at most the locals, FFI state, stack, locals size and store. HOL's
    free `op v ad s res t` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "share_inst_modifies"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem share_inst_modifies {width : Nat} [NeZero width] {C F : Type} (op : WordMemOp) (v : Nat)
    (ad : BitVec width) (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (t : WordSemStateFiniteExact width C F) :
    shareInst (rw := width) op v ad s = (res, t) →
    ∃ (ls : Spt (WordLocW width)) (ffi : HolFfiState F) (stk : List (WordSemStackFrame width))
      (lsz : Option Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      t = { s with locals := ls, ffi := ffi, stack := stk, localsSize := lsz, store := st } := by
  intro h
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] at h <;>
    (repeat' split at h) <;>
    (simp only [Prod.mk.injEq] at h) <;>
    obtain ⟨-, rfl⟩ := h <;>
    exact ⟨_, _, _, _, _, rfl⟩

section StackSizeEvaluate

variable {width : Nat} [NeZero width] {C F : Type}

theorem memStore_stackSize {a : BitVec width} {w : WordLocW width}
    {s t : WordSemStateFiniteExact width C F} (h : memStore a w s = some t) :
    t.stackSize = s.stackSize := by
  unfold memStore at h
  split at h <;> cases h
  rfl

theorem jumpExc_stackSize {s t : WordSemStateFiniteExact width C F} {l : Nat × Nat}
    (h : jumpExc s = some (t, l)) : t.stackSize = s.stackSize := by
  unfold jumpExc at h
  repeat' split at h
  all_goals first | (cases h; rfl) | simp at h

theorem alloc_stackSize (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : (alloc w names s).2.stackSize = s.stackSize :=
  (allocConst w names s (alloc w names s).2 (alloc w names s).1 rfl).2.2.2.2.2.2.2.2.2

theorem shareInst_stackSize (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    (shareInst (rw := width) op v ad s).2.stackSize = s.stackSize := by
  obtain ⟨_, _, _, _, _, h⟩ := share_inst_modifies op v ad s (shareInst (rw := width) op v ad s).1
    (shareInst (rw := width) op v ad s).2 rfl
  rw [h]

theorem popEnv_stackSize {s t : WordSemStateFiniteExact width C F} (h : popEnv s = some t) :
    t.stackSize = s.stackSize := by
  unfold popEnv at h
  split at h <;> cases h <;> rfl

set_option linter.unusedSimpArgs false in
/-- Every statement that neither recurses nor reads the clock keeps the stack-size
    map, except `Install` (Flapjack infrastructure, as `code_evaluate_const`). -/
theorem stackSize_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hni : noInstallSubprogsHOL p = true) :
    (evaluate p s).2.stackSize = s.stackSize := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | rfl
      | exact alloc_stackSize _ _ _
      | exact shareInst_stackSize _ _ _ _
      | (rename_i h; exact inst_stack_size_const_panLang _ _ _ h)
      | (rename_i h; exact memStore_stackSize h)
      | (rename_i h; exact jumpExc_stackSize h)
      | (simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni)

set_option linter.unusedSimpArgs false in
/-- A run of a program without `Install` on a code table without `Install` keeps the
    stack-size map (Flapjack infrastructure; recursion on HOL's termination measure as
    `code_evaluate`, which supplies the code-table invariant). -/
theorem stackSize_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode s.code →
      (evaluate p s).2.stackSize = s.stackSize
  | .tick, s, _, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> rfl
  | .mustTerminate q, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hni
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]
      · simp only [hz, dite_false, if_false]
        have ih := stackSize_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hni hc
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => exact ih
        | some x => cases x <;> first | rfl | exact ih
  | .seq c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      have ih1 := stackSize_evaluate c1 s hni.1 hc
      have hcode := code_evaluate c1 s hni.1 hc
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1 hcode
      have hc1 := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        have hc' : WordProps.noInstallCode s1.code := hcode ▸ hc
        exact (stackSize_evaluate c2 s1 hni.2 hc').trans ih1
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      rcases getVar r1 s with _ | x <;> rcases WordSemStateFiniteExact.getVarImm ri s with _ | y <;> simp only
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;>
        first | rfl | exact stackSize_evaluate c1 s hni.1 hc | exact stackSize_evaluate c2 s hni.2 hc
  | .loop names c exitNames, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hni' := hni
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni'
      rcases hcs : cutState (names, .ln) s with _ | s'
      · rfl
      simp only
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := stackSize_evaluate c { s with locals := l } hni' hc
      have hcode := code_evaluate c { s with locals := l } hni' hc
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at ih hcode
      have hcl := evaluate_clock c _ rb s1 hb
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true]
          exact ih
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          have hcd : WordProps.noInstallCode (decClock s1).code := hcode ▸ hc
          exact (stackSize_evaluate (.loop names c exitNames) (decClock s1) hni hcd).trans ih
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact ih
          · rename_i s2 hce
            obtain ⟨_, rfl⟩ := cutStateConst _ _ _ hce
            exact ih
        · exact ih
  | .call ret dest args handler, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
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
      have hprog := WordProps.noInstallFindCode s.code dest _ _ _ prog _ ⟨hc, hf⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => rfl
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true]; rfl
          simp only [hz, dite_false, if_false]
          have ih := stackSize_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) hprog hc
          rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          simp only
          split
          · exact ih
          · exact ih
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
        · simp only [hz, dite_true, if_true]; rfl
        simp only [hz, dite_false, if_false]
        have hpre : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code :=
          code_pushEnv envs handler _
        have hpreS : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).stackSize = s.stackSize := by
          rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
        have ih := stackSize_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (hpre ▸ hc)
        have hcode := code_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (hpre ▸ hc)
        rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih hcode
        have hcl := evaluate_clock prog _ rc s2 hcv
        have h2 : s2.stackSize = s.stackSize := ih.trans hpreS
        have h2c : s2.code = s.code := hcode.trans hpre
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · exact h2
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]; exact h2
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · exact h2
          simp only
          have h3 : s1.stackSize = s.stackSize := (popEnv_stackSize hp).trans h2
          have h3c : s1.code = s.code :=
            ((popEnvConst _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2c
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · have hcs1 : WordProps.noInstallCode (setVars n ys s1).code := h3c ▸ hc
            exact (stackSize_evaluate retHandler (setVars n ys s1) (noInstall_call_ret hni) hcs1).trans h3
          · exact h3
        · cases handler with
          | none => exact h2
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · exact h2
            · split
              · have hcs2 : WordProps.noInstallCode (setVar n' y s2).code := h2c ▸ hc
                exact (stackSize_evaluate hprog' (setVar n' y s2) (noInstall_call_handler hni) hcs2).trans h2
              · exact h2
        all_goals exact h2
  | .skip, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .move a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .inst a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .assign a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .get a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .set a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .store a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .alloc a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .storeConsts a b c d f, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .raise a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.return a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.break a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.continue a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .opCurrHeap a b c, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .locValue a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .install a b c d f, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .codeBufferWrite a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .dataBufferWrite a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .ffi a b c d f g, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .shareInst a b c, s, hni, _ => stackSize_evaluate_const s _ rfl hni
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, WordSemStateFiniteExact.callEnv, setVars, setVar, pushEnv_clock,
      pushEnv_termdep, true_and] at *
    omega

theorem shareInst_ne_notEnoughSpace (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    (shareInst (rw := width) op v ad s).1 ≠ some .notEnoughSpace := by
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] <;>
    (repeat' split) <;> simp

set_option linter.unusedSimpArgs false in
/-- Only `Alloc` among the statements that neither recurse nor read the clock can
    return `NotEnoughSpace` (Flapjack infrastructure). -/
theorem noSpace_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hni : noInstallSubprogsHOL p = true) (hna : noAllocSubprogsHOL p = true) :
    (evaluate p s).1 ≠ some .notEnoughSpace := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;>
    (try simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni) <;>
    (try simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at hna) <;>
    rw [evaluate] <;>
    (repeat' split) <;>
    first
      | (simp; done)
      | exact shareInst_ne_notEnoughSpace _ _ _ _

set_option linter.unusedSimpArgs false in
/-- A run of a program without `Install` or `Alloc` on a code table without them never
    returns `NotEnoughSpace` (Flapjack infrastructure; recursion on HOL's termination
    measure as `code_evaluate`). -/
theorem noSpace_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      noInstallSubprogsHOL p = true → noAllocSubprogsHOL p = true →
      WordProps.noInstallCode s.code → WordProps.noAllocCode s.code →
      (evaluate p s).1 ≠ some .notEnoughSpace
  | .tick, s, _, _, _, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> simp
  | .mustTerminate q, s, hni, hna, hc, hac => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hni
      simp only [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hna
      by_cases hz : s.termdep = 0
      · simp [hz]
      · simp only [hz, dite_false, if_false]
        have ih := noSpace_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hni hna hc hac
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => simp
        | some x => cases x <;> simp_all
  | .seq c1 c2, s, hni, hna, hc, hac => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      simp only [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hna
      have ih1 := noSpace_evaluate c1 s hni.1 hna.1 hc hac
      have hcode := code_evaluate c1 s hni.1 hc
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1 hcode
      have hc1 := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none => exact noSpace_evaluate c2 s1 hni.2 hna.2 (hcode ▸ hc) (hcode ▸ hac)
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s, hni, hna, hc, hac => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      simp only [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hna
      rcases getVar r1 s with _ | x <;> rcases WordSemStateFiniteExact.getVarImm ri s with _ | y <;>
        simp only <;> try simp
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;>
        first
          | exact noSpace_evaluate c1 s hni.1 hna.1 hc hac
          | exact noSpace_evaluate c2 s hni.2 hna.2 hc hac
          | simp
  | .loop names c exitNames, s, hni, hna, hc, hac => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hni' := hni
      have hna' := hna
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni'
      simp only [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at hna'
      rcases hcs : cutState (names, .ln) s with _ | s'
      · simp
      simp only
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := noSpace_evaluate c { s with locals := l } hni' hna' hc hac
      have hcode := code_evaluate c { s with locals := l } hni' hc
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at ih hcode
      have hcl := evaluate_clock c _ rb s1 hb
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp [hz]
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          exact noSpace_evaluate (.loop names c exitNames) (decClock s1) hni hna (hcode ▸ hc)
            (hcode ▸ hac)
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split <;> simp
        · show wordSemExitLoop rb ≠ _
          cases rb with
          | none => simp [wordSemExitLoop]
          | some r => cases r <;> simp_all [wordSemExitLoop]
  | .call ret dest args handler, s, hni, hna, hc, hac => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
      · simp
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp [hbad]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp
      simp only
      have hprog := WordProps.noInstallFindCode s.code dest _ _ _ prog _ ⟨hc, hf⟩
      have hprogA := WordProps.noAllocFindCode s.code dest _ _ _ prog _ ⟨hf, hac⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => simp
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp [hz]
          simp only [hz, dite_false, if_false]
          have ih := noSpace_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))
            hprog hprogA hc hac
          rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
            ⟨rc, sc⟩
          rw [hcv] at ih
          simp only
          split
          · simp
          · exact ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp [hdc]
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · simp
        simp only
        by_cases hz : s.clock = 0
        · simp [hz]
        simp only [hz, dite_false, if_false]
        have hpre : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).code =
            s.code :=
          code_pushEnv envs handler _
        have ih := noSpace_evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog hprogA (hpre ▸ hc) (hpre ▸ hac)
        have hcode := code_evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) hprog (hpre ▸ hc)
        rcases hcv : evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih hcode
        have hcl := evaluate_clock prog _ rc s2 hcv
        have h2c : s2.code = s.code := hcode.trans hpre
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · simp
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp [hx]
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · simp
          simp only
          have h3c : s1.code = s.code :=
            ((popEnvConst _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2c
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · exact noSpace_evaluate retHandler (setVars n ys s1) (noInstall_call_ret hni)
              (noAlloc_call_ret hna) (h3c ▸ hc) (h3c ▸ hac)
          · simp
        · cases handler with
          | none => simp
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · simp
            · split
              · exact noSpace_evaluate hprog' (setVar n' y s2) (noInstall_call_handler hni)
                  (noAlloc_call_handler hna) (h2c ▸ hc) (h2c ▸ hac)
              · simp
        all_goals (clear ht; simp_all)
  | .skip, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .move a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .inst a, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .assign a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .get a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .set a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .store a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .alloc a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .storeConsts a b c d f, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .raise a, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | WordLangProgHOL.return a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | WordLangProgHOL.break a, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | WordLangProgHOL.continue a, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .opCurrHeap a b c, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .locValue a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .install a b c d f, s, hni, _, _, _ => by
      simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni
  | .codeBufferWrite a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .dataBufferWrite a b, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .ffi a b c d f g, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
  | .shareInst a b c, s, hni, hna, _, _ => noSpace_evaluate_const s _ rfl hni hna
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, WordSemStateFiniteExact.callEnv, setVars, setVar, pushEnv_clock,
      pushEnv_termdep, true_and] at *
    omega

end StackSizeEvaluate

/-- HOL `no_alloc_word_evaluate` (`pan_to_targetProofScript.sml:940-998`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "no_alloc_word_evaluate"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem no_alloc_word_evaluate {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F),
      evaluate prog s = (res, t) ∧ WordProps.noInstallCode s.code ∧ WordProps.noAllocCode s.code ∧
        noInstallSubprogsHOL prog = true ∧ noAllocSubprogsHOL prog = true →
      res ≠ some .notEnoughSpace := by
  rintro prog s res t ⟨h, hc, hac, hni, hna⟩
  have := noSpace_evaluate prog s hni hna hc hac
  rw [h] at this
  exact this

/-- HOL `panLang_wordSem_neq_NotEnoughSpace` (`pan_to_targetProofScript.sml:1000-1024`): a
    clocked start call on the code compiled from Pancake never runs out of space. HOL's free
    `start s k res t pan_code c mc col wprog` are explicit; `word_to_word_compile` is the tagged
    `WordToWord.compile` and `pan_to_word_compile_prog` the tagged `panToWordCompileProgHOL`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "panLang_wordSem_neq_NotEnoughSpace"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem panLang_wordSem_neq_NotEnoughSpace {width : Nat} [NeZero width] {C F State Projection : Type}
    (start : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat)
    (res : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F)
    (panCode : List (DeclHOL width)) (c : Flapjack.Compiler.Backend.Backend.Config)
    (mc : MachineConfig width State Projection) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    evaluate (.call none (some start) [0] none) { s with clock := k } = (res, t) ∧
      ((functionsHOL panCode).map Prod.fst).Nodup ∧
      Compiler.Backend.WordToWord.compile c.wordToWordConf mc.target.config
        (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog) ∧
      s.code = sptFromAList wprog →
    res ≠ some .notEnoughSpace := by
  rintro ⟨h, hd, hcomp, hcode⟩
  let wprog0 := panToWordCompileProgHOL mc.target.config.isa panCode
  have hd0 : (wprog0.map Prod.fst).Nodup := panToWordFirstCompileProgAllDistinctHOL _ panCode hd
  have hni0 := PanToWord.pan_to_word_compile_prog_no_install_code mc.target.config.isa panCode _ rfl
  have hna0 := PanToWord.pan_to_word_compile_prog_no_alloc_code mc.target.config.isa panCode _ rfl
  have hnm0 := PanToWord.pan_to_word_compile_prog_no_mt_code mc.target.config.isa panCode _ rfl
  obtain ⟨hni, hna⟩ := PanToTarget.word_to_word_compile_no_install_no_alloc c.wordToWordConf
    mc.target.config wprog0 col wprog ⟨hcomp, hd0, hnm0, hni0⟩
  refine no_alloc_word_evaluate _ _ res t ⟨h, ?_, ?_, rfl, rfl⟩
  · show WordProps.noInstallCode s.code
    rw [hcode]
    exact hni
  · show WordProps.noAllocCode s.code
    rw [hcode]
    exact hna hna0

/-- HOL `evaluate_stack_size_limit_const_panLang` (`pan_to_targetProofScript.sml:1097-1155`).
    The stack limit is constant for every run (`evaluate_consts`); the stack-size map is
    constant without `Install`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "evaluate_stack_size_limit_const_panLang"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_stack_size_limit_const_panLang {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F),
      evaluate prog s = (res, t) ∧ noInstallSubprogsHOL prog = true ∧
        WordProps.noInstallCode s.code ∧ noAllocSubprogsHOL prog = true ∧
        WordProps.noAllocCode s.code →
      t.stackSize = s.stackSize ∧ t.stackLimit = s.stackLimit := by
  rintro prog s res t ⟨h, hni, hc, -, -⟩
  have hs := stackSize_evaluate prog s hni hc
  rw [h] at hs
  exact ⟨hs, ((evaluate_consts prog s res t h).2.2.2.2.2).symm⟩

/-- HOL `option_lt_SOME` (`pan_to_targetProofScript.sml:1162-1166`); HOL's Boolean equation is
    an `↔` on the tagged `option_lt` (`optionLt`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_SOME"]
theorem option_lt_SOME (x : Option Nat) (n : Nat) :
    optionLt x (some n) = true ↔ ∃ m, x = some m ∧ m < n := by
  cases x <;> simp [optionLt]

end Flapjack.Pancake.Proofs.PanToTarget
