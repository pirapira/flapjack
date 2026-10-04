import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
import Flapjack.Compiler.Backend.WordToStack.NativeSharedMemory
import Flapjack.Misc.Option
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterClock

/-!
# Word-to-Stack `comp_correct`: the `ShareInst` case

`word_to_stackProofScript.sml:7166-7545`, with `word_exp_Op_SOME_Word` (4396).
A shared-memory instruction's address is a variable or a variable plus a
constant; the address register is loaded by `wReg1`, a load writes its result
through `wRegWrite1`, and a store loads its value register by `wReg2`.
Shared-memory accesses are FFI calls, so both sides may end in `FinalFFI`.
-/

namespace Flapjack.WordToStackProofs.CompCorrect.ShareInst
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

/-- HOL `word_exp_Op_SOME_Word` (4396-4400): an operator expression evaluates
only to a word. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_SOME_Word"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wordExpOpSomeWord {width : Nat} [NeZero width] {C F : Type}
    {s : WordSemStateFiniteExact width C F} {op : BinOp}
    {wexps : List (WordLangExpHOL (BitVec width))} {x : WordLocW width} :
    WordSemStateFiniteExact.wordExp s (.op op wexps) = some x → ∃ w, x = .word w := by
  intro h
  simp only [WordSemStateFiniteExact.wordExp] at h
  split at h
  · obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨w, rfl⟩
  · cases h

/-- HOL `flat_exp_conventions_ShareInst_exp_simp` (7166-7173). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "flat_exp_conventions_ShareInst_exp_simp" (words_as_type_indexed_bitvec)]
theorem flatExpConventionsShareInstExpSimp {width : Nat} [NeZero width]
    {op : WordMemOp} {v : Nat} {exp : WordLangExpHOL (BitVec width)} :
    flatExpConventions (.shareInst op v exp : WordLangProgHOL (BitVec width)) = true →
      (∃ ad, exp = .var ad) ∨ (∃ ad offset, exp = .op .add [.var ad, .const offset]) := by
  intro h
  unfold flatExpConventions at h
  split at h <;> simp_all

/-- HOL `word_exp_Op_Add_0` (7175-7184). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_Add_0"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wordExpOpAdd0 {width : Nat} [NeZero width] {C F : Type}
    {s : WordSemStateFiniteExact width C F} {exp : WordLangExpHOL (BitVec width)}
    {x : BitVec width} :
    WordSemStateFiniteExact.wordExp s exp = some (.word x) ↔
      WordSemStateFiniteExact.wordExp s (.op .add [exp, .const 0]) = some (.word x) := by
  rcases h : WordSemStateFiniteExact.wordExp s exp with _ | (w | ⟨a, b⟩) <;>
    simp [WordSemStateFiniteExact.wordExp, h, theWords, wordOpHOL, wordOp]

/-- HOL `evaluate_ShareInst_Var_eq_Op_Add` (7186-7205): a bare variable
address behaves as that variable plus zero. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "evaluate_ShareInst_Var_eq_Op_Add"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateShareInstVarEqOpAdd {width : Nat} [NeZero width] {C F : Type}
    {op : WordMemOp} {v ad : Nat} {s : WordSemStateFiniteExact width C F} :
    WordSemStateFiniteExact.evaluate (.shareInst op v (.var ad)) s =
      WordSemStateFiniteExact.evaluate (.shareInst op v (.op .add [.var ad, .const 0])) s := by
  simp only [WordSemStateFiniteExact.evaluate]
  rcases hv : WordSemStateFiniteExact.wordExp s (.var ad) with _ | (w | ⟨a, b⟩)
  · rcases ho : WordSemStateFiniteExact.wordExp s (.op .add [.var ad, .const 0]) with
      _ | (w' | ⟨a', b'⟩)
    · rfl
    · exact absurd (wordExpOpAdd0.mpr ho) (by simp [hv])
    · rfl
  · rw [wordExpOpAdd0.mp hv]
  · rcases ho : WordSemStateFiniteExact.wordExp s (.op .add [.var ad, .const 0]) with
      _ | (w' | ⟨a', b'⟩)
    · rfl
    · exact absurd (wordExpOpAdd0.mpr ho) (by simp [hv])
    · rfl

/-- Installing the same FFI state on both sides preserves the relation.
Flapjack infrastructure; no separate HOL declaration. -/
theorem stateRelFfi {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (newFfi : HolFfiState F) (related : stateRel ac k f frame source target lens extra) :
    stateRel ac k f frame { source with ffi := newFfi } { target with ffi := newFfi }
      lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  exact ⟨h1,h2,h3,rfl,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,rfl,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩

/-- HOL `share_load_lemma2` (7254-7296): a shared-memory load into a
register-placed variable. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma2"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareLoadLemma2 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < k ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op v ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.shMemSetVar,
      WordSemStateFiniteExact.shMemLoad, WordSemStateFiniteExact.shMemLoadByte,
      WordSemStateFiniteExact.shMemLoad16, WordSemStateFiniteExact.shMemLoad32] at hrun <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemLoadByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemLoad32, r4]
  all_goals
    rw [← r11] at hrun
    split
    · rename_i hD
      split
      · rename_i o hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inr ⟨rfl,
          StateRelRegisterUpdate.stateRelSetVar v _ (stateRelFfi _ related) hv⟩⟩
    · rename_i hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_load_lemma1` (7207-7252): a shared-memory load into a
stack-placed variable, through the scratch register `k`. HOL's `LUPDATE` is
`List.set` and `THE` is `holThe`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareLoadLemma1 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ k ≤ v ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op k ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧
          stateRel ac k f frame s1
            { t1 with stack := (t1.stack.set (t1.stackSpace + (f + k - (v + 1)))
                (Flapjack.holThe (t1.regs.lookup k))) } lens 0 ∧
          (∃ x, t1.regs.lookup k = some x) ∧ t1.stackSpace = t.stackSpace ∧
          t1.stack.length = t.stack.length)) := by
  rintro ⟨hrun, related, hbound, hk, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.shMemSetVar,
      WordSemStateFiniteExact.shMemLoad, WordSemStateFiniteExact.shMemLoadByte,
      WordSemStateFiniteExact.shMemLoad16, WordSemStateFiniteExact.shMemLoad32] at hrun <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemLoadByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemLoad32, r4]
  all_goals
    rw [← r11] at hrun
    split
    · rename_i hD
      split
      · rename_i o hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        refine ⟨_, rfl, .inr ⟨rfl, ?_, ⟨.word (panWordOfBytesHOL false 0 nb),
          by simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩,
          rfl, rfl⟩⟩
        have base := StateRelRegisterUpdate.wordToStackStateRelSetVar2 v
          (.word (panWordOfBytesHOL false 0 nb)) _ _ (stateRelFfi nf related)
          (by omega) hbound rfl rfl
        have := (StateRelRegisterUpdate.stateRelSetVarHigh (ac := ac) (f := f) (frame := frame)
          (lens := lens) (extra := 0) k (.word (panWordOfBytesHOL false 0 nb))
          (Nat.le_refl k)).mpr base
        simpa [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL,
          Flapjack.holThe] using this
    · rename_i hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_store_lemma2` (7348-7384): a shared-memory store of a
register-placed variable. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma2"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareStoreLemma2 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < k ∧
      (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op v ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst] at hrun <;>
    rcases hw : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨a, b⟩) <;>
    simp only [hw, Prod.mk.injEq] at hrun <;>
    try exact absurd hrun.1.symm notError
  all_goals
    have hget : StackSemStateOps.getVar v t = some (.word w) := by
      have := StateRelGetVar.stateRelGetVarImp' ac k f frame s t lens 0 (2 * v) _
        ⟨related, hw, by omega, by omega⟩
      rwa [show 2 * v / 2 = v by omega] at this
    simp only [WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte,
      WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32] at hrun
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemStore16, StackSemShMem.shMemStore32, hget, r4]
    split
    · rename_i hD
      rw [r11] at hD
      simp only [hD, if_true] at hrun
      split
      · rename_i o hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inr ⟨rfl, stateRelFfi nf related⟩⟩
    · rename_i hD
      rw [r11] at hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_store_lemma1` (7298-7346): a shared-memory store of a
stack-placed variable, whose value is first copied from its stack slot into the
scratch register `k+1`. HOL's `EL` is `holEl` and `|+` is `updateEq`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareStoreLemma1 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ ¬ v < k ∧
      (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op (k + 1) ad'
        { t with regs := (t.regs.updateEq
            (k + 1, Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack)) } =
        (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, r35, -, -, -, rloc⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst] at hrun <;>
    rcases hw : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨a, b⟩) <;>
    simp only [hw, Prod.mk.injEq] at hrun <;>
    try exact absurd hrun.1.symm notError
  all_goals
    have hel : Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack = .word w := by
      obtain ⟨-, hplace⟩ := rloc (2 * v) (.word w) hw
      rw [if_neg (by omega)] at hplace
      obtain ⟨hslot, hlt⟩ := hplace
      have hf : f = frame + 1 := by split at r35 <;> omega
      have hidx : f - 1 - (2 * v / 2 - k) = f + k - (v + 1) := by omega
      rw [hidx] at hslot
      simp only [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at hslot
      split at hslot
      · rename_i hin
        obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp hslot
        rw [Flapjack.holEl_eq_getElem _ _ hlen, hval]
      · cases hslot
    have hget : StackSemStateOps.getVar (k + 1)
        { t with regs := (t.regs.updateEq
            (k + 1, Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack)) } =
        some (.word w) := by
      simp [StackSemStateOps.getVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, hel]
    simp only [WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte,
      WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32] at hrun
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemStore16, StackSemShMem.shMemStore32, hget]
    simp only [r4]
    split
    · rename_i hD
      rw [r11] at hD
      simp only [hD, if_true] at hrun
      split
      · rename_i o hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, rfl, r1⟩⟩
      · rename_i nf nb hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        refine ⟨_, rfl, .inr ⟨rfl, ?_⟩⟩
        exact (StateRelRegisterUpdate.stateRelSetVarHigh (k + 1) _ (by omega)).mpr
          (stateRelFfi nf related)
    · rename_i hD
      rw [r11] at hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- The source address `Var r + Const c` (Flapjack infrastructure). -/
theorem wordAddr {width : Nat} [NeZero width] {C F : Type}
    {s : WordSemStateFiniteExact width C F} {r : Nat} {c a : BitVec width} :
    WordSemStateFiniteExact.wordExp s (.op .add [.var r, .const c]) = some (.word a) ↔
      ∃ x, WordSemStateFiniteExact.getVar r s = some (.word x) ∧ a = x + c := by
  rcases h : WordSemStateFiniteExact.getVar r s with _ | (x | ⟨p, q⟩) <;>
    simp [WordSemStateFiniteExact.wordExp, h, theWords, wordOpHOL, wordOp, eq_comm]

/-- The target address `Var r + Const c` (Flapjack infrastructure). -/
theorem stackAddr {width : Nat} [NeZero width] {C F : Type}
    {t : StackSemStateFiniteExact width C F} {r : Nat} {c x : BitVec width}
    (h : StackSemStateOps.getVar r t = some (.word x)) :
    StackSemExpressions.wordExp t (.op .add [.var r, .const c]) = some (x + c) := by
  simp [StackSemExpressions.wordExp, StackSemStateOps.getVar] at h ⊢
  simp [h, wordOpHOL, wordOp]

/-- Source decomposition of a nonerror `ShareInst` with a `Var + Const`
address (Flapjack infrastructure). -/
theorem shareInstSource {width : Nat} [NeZero width] {C F : Type}
    {op : WordMemOp} {v ad : Nat} {offset : BitVec width}
    {s s1 : WordSemStateFiniteExact width (Nat × C) F} {res : Option (WordSemResult width)}
    (hrun : WordSemStateFiniteExact.evaluate
      (.shareInst op v (.op .add [.var ad, .const offset])) s = (res, s1))
    (notError : res ≠ some .error) :
    ∃ x, WordSemStateFiniteExact.getVar ad s = some (.word x) ∧
      WordSemStateFiniteExact.shareInst op v (x + offset) s = (res, s1) := by
  simp only [WordSemStateFiniteExact.evaluate] at hrun
  rcases he : WordSemStateFiniteExact.wordExp s (.op .add [.var ad, .const offset]) with
      _ | (a | ⟨p, q⟩) <;> simp only [he, Prod.mk.injEq] at hrun
  · exact absurd hrun.1.symm notError
  · obtain ⟨x, hx, rfl⟩ := wordAddr.mp he
    exact ⟨x, hx, hrun⟩
  · exact absurd hrun.1.symm notError

/-- Target shared-memory operations leave the clock unchanged (Flapjack
infrastructure). -/
theorem shMemOp_clock {width : Nat} [NeZero width] {C F : Type} (op : WordMemOp) (r : Nat)
    (a : BitVec width) (u : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemOp op r a u).2.clock = u.clock := by
  cases op <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemLoadByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemLoad32, StackSemShMem.shMemStore,
      StackSemShMem.shMemStoreByte, StackSemShMem.shMemStore16, StackSemShMem.shMemStore32] <;>
    repeat' split
  all_goals rfl

/-- HOL `evaluate_ShareInst_Load` (7386-7445). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_Load"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateShareInstLoad {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) →
    ∃ ck t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := ck + t.clock }) = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, notError, related, hv, had, hop⟩
  obtain ⟨x, hx, hshare⟩ := shareInstSource hrun notError
  rcases fmt : Compiler.Backend.WordToStackRegFormat.wReg1 (2 * ad) (k, f, frame) with ⟨xs, reg⟩
  obtain ⟨t1, run1, clock1, rel1, len1, sp1, -, -, -, loaded⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame (2 * ad) reg xs s t lens (.word x) fmt
      (by omega) hx related
  refine ⟨1, ?_⟩
  have hloads : StackSemEvaluate.evaluate (wStackLoadNative xs .skip,
      { t with clock := 1 + t.clock }) = (none, { t1 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run1]; rfl
  have hfix : StackSemControl.fixClock { t with clock := 1 + t.clock }
      ((none : Option (StackSemResult width)), { t1 with clock := 1 + t.clock }) =
      (none, { t1 with clock := 1 + t.clock }) := by
    simp [StackSemControl.fixClock]
  have hdec : StackSemStateOps.decClock { t1 with clock := 1 + t.clock } = t1 := by
    simp only [StackSemStateOps.decClock, clock1]
    congr 1
    omega
  have haddr : StackSemExpressions.wordExp { t1 with clock := 1 + t.clock }
      (.op .add [.var reg, .const offset]) = some (x + offset) :=
    stackAddr (t := { t1 with clock := 1 + t.clock }) loaded
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [wShareInstNative, fmt] <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hloads, hfix] <;>
    simp only [wRegWrite1Native, show 2 * v / 2 = v by omega]
  all_goals
    split
    · rename_i hlt
      rw [StackSemEvaluate.evaluate_shMemOp, haddr]
      simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec]
      exact shareLoadLemma2 ⟨hshare, rel1, hlt, by simp, notError⟩
    · rename_i hge
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_shMemOp, haddr]
      simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec]
      obtain ⟨t2, h2, hc⟩ := shareLoadLemma1 ⟨hshare, rel1, hv, by omega, by simp, notError⟩
      have hclk : t2.clock = t.clock := by
        have hc' := congrArg (fun p => p.2.clock) h2
        simp only [shMemOp_clock] at hc'
        omega
      have hmin : min (1 + t.clock) t2.clock = t2.clock := by omega
      rw [h2]
      have hfix2 : ∀ r : Option (StackSemResult width), StackSemControl.fixClock
          { t1 with clock := 1 + t.clock } (r, t2) = (r, t2) := by
        intro r
        show (r, { t2 with clock := min (1 + t.clock) t2.clock }) = (r, t2)
        rw [hmin]
      rw [hfix2]
      have related' := related
      unfold stateRel at related'
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, -, -, r33, -, r35, -⟩ := related'
      rcases hc with ⟨fv, rfl, hffi, hcl⟩ | ⟨rfl, hrel, ⟨xv, hxv⟩, hsp, hlen⟩
      · exact ⟨t2, rfl, .inl ⟨fv, rfl, hffi, hcl⟩⟩
      · have huse : t2.useStack = true := by
          have hrel' := hrel
          unfold stateRel at hrel'
          exact hrel'.2.2.2.2.1
        have hf : f = frame + 1 := by split at r35 <;> omega
        have hidx : f - 1 - (v - k) = f + k - (v + 1) := by omega
        refine ⟨_, ?_, .inr ⟨rfl, hrel⟩⟩
        simp only [Option.map_none]
        rw [StackSemEvaluate.evaluate_stackStore]
        simp only [huse, Bool.not_true, Bool.false_eq_true, if_false,
          StackSemStateOps.getVar, hxv, hidx, Flapjack.holThe]
        rw [if_neg (by omega)]

/-- A shared-memory store from any target register holding the stored source
word (Flapjack factoring of `share_store_lemma1`/`share_store_lemma2` after the
operand loads; no separate HOL declaration). -/
theorem shareStoreGeneric {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v r : Nat}
    {ad' w : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)}
    (hrun : WordSemStateFiniteExact.shareInst op v ad' s = (res, s1))
    (related : stateRel ac k f frame s t lens 0)
    (hw : WordSemStateFiniteExact.getVar v s = some (.word w))
    (hget : StackSemStateOps.getVar r t = some (.word w))
    (hop : op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32)
    (notError : res ≠ some .error) :
    ∃ t1, StackSemShMem.shMemOp op r ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst, hw, WordSemStateFiniteExact.shMemStore,
      WordSemStateFiniteExact.shMemStoreByte, WordSemStateFiniteExact.shMemStore16,
      WordSemStateFiniteExact.shMemStore32] at hrun <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemStore16, StackSemShMem.shMemStore32, hget]
  all_goals
    simp only [r4]
    split
    · rename_i hD
      rw [r11] at hD
      simp only [hD, if_true] at hrun
      split
      · rename_i o hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inr ⟨rfl, stateRelFfi nf related⟩⟩
    · rename_i hD
      rw [r11] at hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `evaluate_ShareInst_Store` (7447-7499). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_ShareInst_Store"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateShareInstStore {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k ∧
      res ≠ some .error ∧ (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
    ∃ ck t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := ck + t.clock }) = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, had, notError, hop⟩
  obtain ⟨x, hx, hshare⟩ := shareInstSource hrun notError
  -- The stored source word.
  have hw : ∃ w, WordSemStateFiniteExact.getVar (2 * v) s = some (.word w) := by
    rcases hg : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨p, q⟩)
    all_goals first
      | exact ⟨w, rfl⟩
      | (rcases hop with rfl | rfl | rfl | rfl <;>
          simp only [WordSemStateFiniteExact.shareInst, hg, Prod.mk.injEq] at hshare <;>
          exact absurd hshare.1.symm notError)
  obtain ⟨w, hw⟩ := hw
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 (2 * ad) (k, f, frame) with
    ⟨xs, reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 (2 * v) (k, f, frame) with
    ⟨ys, reg2⟩
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame (2 * ad) reg1 xs s t lens (.word x) fmt1
      (by omega) hx related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame (2 * v) reg2 ys s t1 lens (.word w) fmt2
      (by omega) hw rel1
  refine ⟨1, ?_⟩
  have hl1 : StackSemEvaluate.evaluate (wStackLoadNative xs .skip,
      { t with clock := 1 + t.clock }) = (none, { t1 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run1]; rfl
  have hl2 : StackSemEvaluate.evaluate (wStackLoadNative ys .skip,
      { t1 with clock := 1 + t.clock }) = (none, { t2 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run2]; rfl
  have hfix : ∀ (u u' : StackSemStateFiniteExact width C F), StackSemControl.fixClock
      { u with clock := 1 + t.clock }
      ((none : Option (StackSemResult width)), { u' with clock := 1 + t.clock }) =
      (none, { u' with clock := 1 + t.clock }) := by
    intro u u'; simp [StackSemControl.fixClock]
  have hdec : StackSemStateOps.decClock { t2 with clock := 1 + t.clock } = t2 := by
    simp only [StackSemStateOps.decClock]
    congr 1
    omega
  have read1 : StackSemStateOps.getVar reg1 t2 = some (.word x) := by
    rw [otherReads reg1 regNe]; exact loaded1
  have haddr : StackSemExpressions.wordExp { t2 with clock := 1 + t.clock }
      (.op .add [.var reg1, .const offset]) = some (x + offset) :=
    stackAddr (t := { t2 with clock := 1 + t.clock }) read1
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [wShareInstNative, fmt1, fmt2, wStackLoadAppend, Function.comp_apply] <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hl1, hfix] <;>
    dsimp only <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hl2, hfix] <;>
    dsimp only <;>
    rw [StackSemEvaluate.evaluate_shMemOp, haddr] <;>
    simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec] <;>
    exact shareStoreGeneric hshare rel2 hw loaded2 (by simp) notError

/-- HOL `evaluate_ShareInst_correct_lemma` (7501-7526). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "evaluate_ShareInst_correct_lemma"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateShareInstCorrectLemma {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k →
    ∃ ck t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := ck + t.clock }) = (res.map compileResult, t1) ∧
      ((res = none ∧ stateRel ac k f frame s1 t1 lens 0) ∨
        (∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock)) := by
  rintro ⟨hrun, notError, related, hv, had⟩
  have swap : ∀ ck t1, (StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := ck + t.clock }) = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0))) →
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := ck + t.clock }) = (res.map compileResult, t1) ∧
      ((res = none ∧ stateRel ac k f frame s1 t1 lens 0) ∨
        (∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock)) :=
    fun _ _ ⟨h, hc⟩ => ⟨h, hc.symm⟩
  cases op
  case load | load8 | load16 | load32 =>
    obtain ⟨ck, t1, h⟩ := evaluateShareInstLoad ⟨hrun, notError, related, hv, had, by simp⟩
    exact ⟨ck, t1, swap ck t1 h⟩
  case store | store8 | store16 | store32 =>
    obtain ⟨ck, t1, h⟩ := evaluateShareInstStore ⟨hrun, related, hv, had, notError, by simp⟩
    exact ⟨ck, t1, swap ck t1 h⟩

/-- Full original comp_correct ShareInst case (`word_to_stackProofScript.sml:7528-7545`).
All original premises and the complete target clock/run/result/resource
conclusion are retained; no target run, simulation law or successful-execution
restriction is assumed. Evaluator closure inherits reals_as_rational_cuts; no
numerical FP assertion. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectShareInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.shareInst op v exp) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, -, -, -, -,
    maxBound⟩ := premises
  rcases flatExpConventionsShareInstExpSimp flat with ⟨ad, rfl⟩ | ⟨ad, offset, rfl⟩
  all_goals
    simp [postAllocConventionsHOL, everyVarHOL, everyVarExpHOL, everyVarExpsHOL,
      everyStackVarHOL, callArgConventionHOL, isPhyVar] at conventions
    simp [maxVarHOL, maxVarExpHOL, maxList] at maxBound
    simp only [compNative, expToAddrHOL, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -, -⟩ := compilation
  case inl =>
    rw [evaluateShareInstVarEqOpAdd] at execution
    obtain ⟨v', rfl⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', ad = 2 * a' := ⟨ad / 2, by omega⟩
    obtain ⟨ck, t1, h, hc⟩ :=
      evaluateShareInstCorrectLemma ⟨execution, notError, related, by omega, by omega⟩
    refine ⟨ck, t1, result.map compileResult, ?_, ?_⟩
    · rw [Nat.add_comm]; simpa [HolAddr.ofWordLangAddr] using h
    · rcases hc with ⟨rfl, hr⟩ | ⟨fv, rfl, hffi, hclk⟩
      · simpa [compCorrectResult] using hr
      · simp [compCorrectResult, hffi, hclk]
  case inr =>
    obtain ⟨v', rfl⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', ad = 2 * a' := ⟨ad / 2, by omega⟩
    obtain ⟨ck, t1, h, hc⟩ :=
      evaluateShareInstCorrectLemma ⟨execution, notError, related, by omega, by omega⟩
    refine ⟨ck, t1, result.map compileResult, ?_, ?_⟩
    · rw [Nat.add_comm]; simpa [HolAddr.ofWordLangAddr] using h
    · rcases hc with ⟨rfl, hr⟩ | ⟨fv, rfl, hffi, hclk⟩
      · simpa [compCorrectResult] using hr
      · simp [compCorrectResult, hffi, hclk]

end Flapjack.WordToStackProofs.CompCorrect.ShareInst
