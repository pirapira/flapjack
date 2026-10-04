import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.FpArith
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.CarryOverflow
import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister2

/-! Original evaluate_wInst FP branch (word_to_stackProofScript.sml 5025-5130):
the FP/integer register transfer cases FPMovToReg (single write at width 64,
the double write through wRegWrite2 otherwise) and FPMovFromReg (one or two
integer reads through wStackLoad). -/
namespace Flapjack.WordToStackProofs.InstSimulation.FpTransfer
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

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

/-- HOL `word_extract 31 0` of a word64 is the low 32-bit slice. -/
private theorem extractLow {width : Nat} (v : BitVec 64) :
    (v.extractLsb' 0 32).setWidth width = holWordExtract 31 0 v width := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb']

/-- HOL `word_extract 63 32` of a word64 is the high 32-bit slice. -/
private theorem extractHigh {width : Nat} (v : BitVec 64) :
    (v.extractLsb' 32 32).setWidth width = holWordExtract 63 32 v width := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb']

/-- Flapjack infrastructure: a successful spill-store sequence commutes with
a register update the stores do not read. -/
private theorem stackStoreSetVar {width : Nat} [NeZero width] {C F : Type}
    (loads : List (Nat × Nat)) (p : Nat) (v : WordLocW width)
    (x y : StackSemStateFiniteExact width C F)
    (distinct : ∀ e ∈ loads, e.1 ≠ p)
    (run : StackSemEvaluate.evaluate (wStackStoreNative loads .skip, x) = (none, y)) :
    StackSemEvaluate.evaluate (wStackStoreNative loads .skip, StackSemStateOps.setVar p v x) =
      (none, StackSemStateOps.setVar p v y) := by
  induction loads generalizing y with
  | nil =>
    simp only [wStackStoreNative, StackSemEvaluate.evaluate_skip, Prod.mk.injEq] at run ⊢
    rw [run.2]
    exact ⟨trivial, rfl⟩
  | cons entry tail ih =>
    rcases entry with ⟨r, n⟩
    have rp : r ≠ p := distinct (r, n) (by simp)
    simp only [wStackStoreNative] at run ⊢
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run ⊢
    rcases first : StackSemEvaluate.evaluate (wStackStoreNative tail .skip, x) with ⟨res, x1⟩
    rw [first] at run
    cases res with
    | some e => simp at run
    | none =>
      rw [ih x1 (fun e he => distinct e (List.mem_cons_of_mem _ he)) first]
      simp only at run ⊢
      rw [StackSemEvaluate.evaluate_stackStore] at run ⊢
      have getSame : StackSemStateOps.getVar r (StackSemStateOps.setVar p v x1) =
          StackSemStateOps.getVar r x1 := by
        simp [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
          FUPDATE_HOL, rp]
      rw [getSame]
      by_cases use : x1.useStack = true
      · by_cases room : x1.stack.length ≤ x1.stackSpace + n
        · simp [use, room] at run
        · cases hr : StackSemStateOps.getVar r x1 with
          | none => simp [use, room, hr] at run
          | some value =>
            simp only [use, room, hr, Bool.not_true, Bool.false_eq_true, if_false,
              Prod.mk.injEq, true_and] at run
            subst run
            simp [StackSemStateOps.setVar, use, room]
      · simp [use] at run

/-- Full original evaluate_wInst FPMovFromReg case (FP branch 5025-5130):
all five guards, actual native run, full stateRel and stack resources. At
width 64 one integer register is loaded through wReg1 (the second register is
ignored, as in HOL's wInst and inst); otherwise both registers are loaded
through wReg1/wReg2 and concatenated high ++ low. Source reads and success are
derived internally; the FP update uses state_rel_set_fp_var. Canonical maps
and word widths are qualified; evaluators inherit reals_as_rational_cuts
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpMovFromReg {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d r1 r2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpMovFromReg d r1 r2)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp (.fpMovFromReg d r1 r2) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpMovFromReg d r1 r2) : WordLangInst (BitVec width)) < 2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpMovFromReg d r1 r2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpMovFromReg d r1 r2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  by_cases hw : width = 64
  · have even : r1 % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar, hw] using physical
    cases h1 : WordSemStateFiniteExact.getVar r1 source with
    | none => simp [WordSemStateFiniteExact.inst, hw, h1] at executed
    | some a =>
      cases a with
      | loc l n => simp [WordSemStateFiniteExact.inst, hw, h1] at executed
      | word w1 =>
        simp only [WordSemStateFiniteExact.inst, hw, if_true, h1, Option.some.injEq] at executed
        rcases compiled : wReg1 r1 (k,f,frame) with ⟨loads, reg⟩
        obtain ⟨loaded, loadRun, loadClock, loadedRel, loadedLength, loadedSpace, _, _, _,
            regValue⟩ :=
          LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg loads source target lens
            (.word w1) compiled even h1 related
        refine ⟨StackSemStateOps.setFpVar d (w1.setWidth 64) loaded, ?_, ?_, loadedLength,
          loadedSpace⟩
        · simp only [wInstNative, hw, if_true, compiled, List.append_nil]
          rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq,
            StackSemEvaluateClock.fixClockEvaluate, loadRun]
          simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister, hw,
            regValue]
        · rw [← executed]
          exact StateRelFp.stateRelSetFpVar ac k f frame source loaded lens 0 d _ loadedRel
  · have evens : r1 % 2 = 0 ∧ r2 % 2 = 0 := by
      simpa [everyVarInstHOL, isPhyVar, hw] using physical
    cases h1 : WordSemStateFiniteExact.getVar r1 source with
    | none => simp [WordSemStateFiniteExact.inst, hw, h1] at executed
    | some a =>
      cases a with
      | loc l n => simp [WordSemStateFiniteExact.inst, hw, h1] at executed
      | word w1 =>
        cases h2 : WordSemStateFiniteExact.getVar r2 source with
        | none => simp [WordSemStateFiniteExact.inst, hw, h1, h2] at executed
        | some b =>
          cases b with
          | loc l n => simp [WordSemStateFiniteExact.inst, hw, h1, h2] at executed
          | word w2 =>
            simp only [WordSemStateFiniteExact.inst, hw, if_false, h1, h2,
              Option.some.injEq] at executed
            rcases compiled1 : wReg1 r1 (k,f,frame) with ⟨loads1, reg1⟩
            rcases compiled2 : wReg2 r2 (k,f,frame) with ⟨loads2, reg2⟩
            obtain ⟨loaded, loadRun, loadClock, loadedRel, loadedLength, loadedSpace,
                value1, value2⟩ :=
              CarryOverflow.loadOperands ac k f frame r1 r2 reg1 reg2 loads1 loads2 source
                target lens (.word w1) (.word w2) compiled1 compiled2 evens.1 evens.2 h1 h2
                related
            refine ⟨StackSemStateOps.setFpVar d ((w2 ++ w1).setWidth 64) loaded, ?_, ?_,
              loadedLength, loadedSpace⟩
            · simp only [wInstNative, hw, if_false, compiled1, compiled2]
              rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq,
                StackSemEvaluateClock.fixClockEvaluate, loadRun]
              simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
                StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister,
                hw, value1, value2]
            · rw [← executed]
              exact StateRelFp.stateRelSetFpVar ac k f frame source loaded lens 0 d _ loadedRel

/-- Full original evaluate_wInst FPMovToReg case (FP branch 5025-5130),
including HOL's only double write: all five guards, actual native run, full
stateRel and stack resources. At width 64 the FP word is written through
wRegWrite1; otherwise the low half is written through the inner wRegWrite1 and
the high half through the outer wRegWrite2, exactly as in the original proof
(evaluate_wRegWrite2_seq, evaluate_wStackStore_wReg2_new, state_rel_set_var).
The source/target halves agree via word_extract = extractLsb'. Canonical maps
and word widths are qualified; evaluators inherit reals_as_rational_cuts
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpMovToReg {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 d k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpMovToReg r1 r2 d)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp (.fpMovToReg r1 r2 d) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.fp (.fpMovToReg r1 r2 d) : WordLangInst (BitVec width)) < 2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpMovToReg r1 r2 d) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpMovToReg r1 r2 d)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 d related
  cases hd : WordSemStateFiniteExact.getFpVar d source with
  | none => simp [WordSemStateFiniteExact.inst, hd] at executed
  | some v =>
  have td : StackSemStateOps.getFpVar d target = some v := read.symm.trans hd
  by_cases hw : width = 64
  · have even : r1 % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar, hw] using physical
    have range : r1 < 2 * frame + 2 * k := by simpa [maxVarInstHOL, hw] using bound
    simp only [WordSemStateFiniteExact.inst, hd, hw, if_true, Option.some.injEq] at executed
    rcases compiled : wReg1 r1 (k,f,frame) with ⟨loads, reg⟩
    obtain ⟨post, run, postRel, lengthEq, spaceEq⟩ :=
      StoreRegister.evaluateWStackStoreWReg1 ac r1 reg k f frame loads source target lens
        (.word (v.setWidth width)) target.stack.length target.stackSpace compiled even range
        related rfl rfl
    refine ⟨post, ?_, executed ▸ postRel, lengthEq, spaceEq⟩
    simp only [wInstNative, hw, if_true, StoreRegister.evaluateWRegWrite1Seq, compiled]
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    simpa [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemFpInstructions.instFp,
      StackSemFpRegisterInstructions.instFpRegister, hw, td] using run
  · have evens : r1 % 2 = 0 ∧ r2 % 2 = 0 := by
      simpa [everyVarInstHOL, isPhyVar, hw] using physical
    have ranges : r1 < 2 * frame + 2 * k ∧ r2 < 2 * frame + 2 * k := by
      simp only [maxVarInstHOL, hw, if_false] at bound
      omega
    simp only [WordSemStateFiniteExact.inst, hd, hw, if_false, Option.some.injEq,
      ← extractLow, ← extractHigh] at executed
    let lo : WordLocW width := .word ((v.extractLsb' 0 32).setWidth width)
    let hi : WordLocW width := .word ((v.extractLsb' 32 32).setWidth width)
    rcases compiled1 : wReg1 r1 (k,f,frame) with ⟨loads1, p1⟩
    rcases compiled2 : wReg2 r2 (k,f,frame) with ⟨loads2, p2⟩
    have spillRegister : ∀ e ∈ loads1, e.1 = k := by
      intro e he
      simp only [wReg1] at compiled1
      split at compiled1
      · simp only [Prod.mk.injEq] at compiled1
        rw [← compiled1.1] at he
        simp at he
      · simp only [Prod.mk.injEq] at compiled1
        rw [← compiled1.1] at he
        simp only [List.mem_singleton] at he
        rw [he]
    have secondNe : p2 ≠ k := by
      simp only [wReg2] at compiled2
      split at compiled2 <;> simp only [Prod.mk.injEq] at compiled2 <;> omega
    have stores1 : ∀ e ∈ loads1, e.1 ≠ p2 := fun e he => (spillRegister e he).symm ▸ secondNe.symm
    obtain ⟨base, baseRun, baseRel, baseLength, baseSpace⟩ :=
      StoreRegister.evaluateWStackStoreWReg1 ac r1 p1 k f frame loads1 source target lens lo
        target.stack.length target.stackSpace compiled1 evens.1 ranges.1 related rfl rfl
    have innerRun : StackSemEvaluate.evaluate
        (wRegWrite1Native (fun r1 => .inst (.fp (.fpMovToReg r1 p2 d))) r1 (k,f,frame), target) =
        (none, StackSemStateOps.setVar p2 hi base) := by
      simp only [StoreRegister.evaluateWRegWrite1Seq, compiled1]
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
      have primitive : StackSemEvaluate.evaluate
          ((.inst (.fp (.fpMovToReg p1 p2 d)) : HolProg width), target) =
          (none, StackSemStateOps.setVar p2 hi (StackSemStateOps.setVar p1 lo target)) := by
        simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister, hw, td,
          lo, hi]
      rw [primitive]
      exact stackStoreSetVar loads1 p2 hi _ base stores1 baseRun
    obtain ⟨post, run, postRel, lengthEq, spaceEq⟩ :=
      StoreRegister2.evaluateWStackStoreWReg2New ac r2 p2 k f frame loads2
        (wRegWrite1Native (fun r1 => .inst (.fp (.fpMovToReg r1 p2 d))) r1 (k,f,frame))
        (WordSemStateFiniteExact.setVar r1 lo source) target lens hi target.stack.length
        target.stackSpace ⟨compiled2, evens.2, ranges.2, base, innerRun, baseRel, baseLength,
          baseSpace⟩
    refine ⟨post, ?_, executed ▸ postRel, lengthEq, spaceEq⟩
    simp only [wInstNative, hw, if_false, StoreRegister2.evaluateWRegWrite2Seq, compiled2]
    exact run

end Flapjack.WordToStackProofs.InstSimulation.FpTransfer
