import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelFp
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement

/-! Original evaluate_wInst FP branch (word_to_stackProofScript.sml 5025-5130):
the FP comparison cases FPLess/FPLessEqual/FPEqual, which write an integer
register through wRegWrite1, and the pass-through FP-register cases
FPMov/FPAbs/FPNeg/FPSqrt/FPAdd/FPSub/FPMul/FPDiv/FPFma, which wInst emits
unchanged. These are the generic tail of the original FP proof. -/
namespace Flapjack.WordToStackProofs.InstSimulation.FpArith
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

/-- Flapjack factoring of the pass-through FP cases: wInst emits the source
instruction unchanged, and both primitive semantics update the same FP
register with the same word64. No target-run or postrelation premise. -/
private theorem passThrough {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : HolFp) (k f frame d : Nat) (x : BitVec 64)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (compiled : wInstNative (.fp op : HolInst width) (k,f,frame) = (.inst (.fp op) : HolProg width))
    (targetStep : StackSemInst.instHOL (.fp op) target = some (StackSemStateOps.setFpVar d x target))
    (sourceEq : WordSemStateFiniteExact.setFpVar d x source = sourcePost)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp op : HolInst width) (k,f,frame), target) = (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  refine ⟨StackSemStateOps.setFpVar d x target, ?_, ?_, rfl, rfl⟩
  · rw [compiled, StackSemEvaluate.evaluate_inst, targetStep]
  · rw [← sourceEq]
    exact StateRelFp.stateRelSetFpVar ac k f frame source target lens 0 d x related

/-- Flapjack factoring of the FP comparison cases: the compiled wRegWrite1
writes the comparison bit to the physical register or its spill slot through
the accepted Reg1 store law. -/
private theorem compareWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register k f frame : Nat) (bit : Bool)
    (kont : Nat → HolProg width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (targetStep : ∀ reg, StackSemEvaluate.evaluate (kont reg, target) =
      (none, StackSemStateOps.setVar reg
        (.word (if bit then BitVec.ofNat width 1 else BitVec.ofNat width 0)) target))
    (sourceEq : WordSemStateFiniteExact.setVar register
      (.word (if bit then 1 else 0)) source = sourcePost)
    (even : register % 2 = 0) (range : register < 2 * frame + 2 * k)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wRegWrite1Native kont register (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  rcases compiled : wReg1 register (k,f,frame) with ⟨loads, reg⟩
  obtain ⟨post, run, postRel, lengthEq, spaceEq⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac register reg k f frame loads source target lens
      (.word (if bit then 1 else 0)) target.stack.length target.stackSpace compiled even range
      related rfl rfl
  refine ⟨post, ?_, sourceEq ▸ postRel, lengthEq, spaceEq⟩
  simp only [StoreRegister.evaluateWRegWrite1Seq, compiled]
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetStep]
  have same : (if bit then BitVec.ofNat width 1 else BitVec.ofNat width 0) =
      (if bit then (1 : BitVec width) else 0) := by cases bit <;> rfl
  simpa only [same, StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self] using run

/-- Full original evaluate_wInst FPLess case (FP branch 5025-5130, generic
tail): all five guards, actual native run, full stateRel and stack resources.
The FP operand reads are derived from the relation (state_rel_get_fp_var);
the comparison bit is written through wRegWrite1. Canonical maps and word
widths are qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpLess {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpLess r d1 d2)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp (.fpLess r d1 d2) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.fp (.fpLess r d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpLess r d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpLess r d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : r % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar] using physical
  have range : r < 2 * frame + 2 * k := bound
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h1 : WordSemStateFiniteExact.getFpVar d1 source with
  | none => simp [WordSemStateFiniteExact.inst, h1] at executed
  | some x1 =>
    cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
    | none => simp [WordSemStateFiniteExact.inst, h1, h2] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h1, h2, Option.some.injEq] at executed
      have t1 := (read d1).symm.trans h1
      have t2 := (read d2).symm.trans h2
      exact compareWrite ac r k f frame (holFp64LessThan x1 x2)
        (fun r => .inst (.fp (.fpLess r d1 d2))) source sourcePost target lens
        (fun reg => by
          simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister,
            t1, t2])
        (by simpa using executed) even range related

/-- Full original evaluate_wInst FPLessEqual case (FP branch 5025-5130, generic
tail): all five guards, actual native run, full stateRel and stack resources.
The FP operand reads are derived from the relation (state_rel_get_fp_var);
the comparison bit is written through wRegWrite1. Canonical maps and word
widths are qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpLessEqual {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpLessEqual r d1 d2)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp (.fpLessEqual r d1 d2) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.fp (.fpLessEqual r d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpLessEqual r d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpLessEqual r d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : r % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar] using physical
  have range : r < 2 * frame + 2 * k := bound
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h1 : WordSemStateFiniteExact.getFpVar d1 source with
  | none => simp [WordSemStateFiniteExact.inst, h1] at executed
  | some x1 =>
    cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
    | none => simp [WordSemStateFiniteExact.inst, h1, h2] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h1, h2, Option.some.injEq] at executed
      have t1 := (read d1).symm.trans h1
      have t2 := (read d2).symm.trans h2
      exact compareWrite ac r k f frame (holFp64LessEqual x1 x2)
        (fun r => .inst (.fp (.fpLessEqual r d1 d2))) source sourcePost target lens
        (fun reg => by
          simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister,
            t1, t2])
        (by simpa using executed) even range related

/-- Full original evaluate_wInst FPEqual case (FP branch 5025-5130, generic
tail): all five guards, actual native run, full stateRel and stack resources.
The FP operand reads are derived from the relation (state_rel_get_fp_var);
the comparison bit is written through wRegWrite1. Canonical maps and word
widths are qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpEqual {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpEqual r d1 d2)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp (.fpEqual r d1 d2) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.fp (.fpEqual r d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpEqual r d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpEqual r d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : r % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar] using physical
  have range : r < 2 * frame + 2 * k := bound
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h1 : WordSemStateFiniteExact.getFpVar d1 source with
  | none => simp [WordSemStateFiniteExact.inst, h1] at executed
  | some x1 =>
    cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
    | none => simp [WordSemStateFiniteExact.inst, h1, h2] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h1, h2, Option.some.injEq] at executed
      have t1 := (read d1).symm.trans h1
      have t2 := (read d2).symm.trans h2
      exact compareWrite ac r k f frame (holFp64Equal x1 x2)
        (fun r => .inst (.fp (.fpEqual r d1 d2))) source sourcePost target lens
        (fun reg => by
          simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemFpInstructions.instFp, StackSemFpRegisterInstructions.instFpRegister,
            t1, t2])
        (by simpa using executed) even range related

/-- Full original evaluate_wInst FPMov case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpMov {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpMov d1 d2)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpMov d1 d2) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpMov d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpMov d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpMov d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x =>
    simp only [WordSemStateFiniteExact.inst, h2, Option.some.injEq] at executed
    have t2 := (read d2).symm.trans h2
    exact passThrough ac (.fpMov d1 d2) k f frame d1 (x) source sourcePost target lens rfl
      (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
        StackSemFpRegisterInstructions.instFpRegister, t2]) executed related

/-- Full original evaluate_wInst FPAbs case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpAbs {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpAbs d1 d2)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpAbs d1 d2) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpAbs d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpAbs d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpAbs d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x =>
    simp only [WordSemStateFiniteExact.inst, h2, Option.some.injEq] at executed
    have t2 := (read d2).symm.trans h2
    exact passThrough ac (.fpAbs d1 d2) k f frame d1 (holFp64Abs x) source sourcePost target lens rfl
      (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
        StackSemFpRegisterInstructions.instFpRegister, t2]) executed related

/-- Full original evaluate_wInst FPNeg case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpNeg {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpNeg d1 d2)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpNeg d1 d2) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpNeg d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpNeg d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpNeg d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x =>
    simp only [WordSemStateFiniteExact.inst, h2, Option.some.injEq] at executed
    have t2 := (read d2).symm.trans h2
    exact passThrough ac (.fpNeg d1 d2) k f frame d1 (holFp64Negate x) source sourcePost target lens rfl
      (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
        StackSemFpRegisterInstructions.instFpRegister, t2]) executed related

/-- Full original evaluate_wInst FPSqrt case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpSqrt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpSqrt d1 d2)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpSqrt d1 d2) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpSqrt d1 d2) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpSqrt d1 d2) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpSqrt d1 d2)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x =>
    simp only [WordSemStateFiniteExact.inst, h2, Option.some.injEq] at executed
    have t2 := (read d2).symm.trans h2
    exact passThrough ac (.fpSqrt d1 d2) k f frame d1 (holFp64Sqrt .roundTiesToEven x) source sourcePost target lens rfl
      (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
        StackSemFpRegisterInstructions.instFpRegister, StackSemFpRegisterInstructions.instFpSqrt,
        holFp64Sqrt_agreement, t2]) executed related

/-- Full original evaluate_wInst FPAdd case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpAdd {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 d3 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpAdd d1 d2 d3)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpAdd d1 d2 d3) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpAdd d1 d2 d3) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpAdd d1 d2 d3) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpAdd d1 d2 d3)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x1 =>
    cases h3 : WordSemStateFiniteExact.getFpVar d3 source with
    | none => simp [WordSemStateFiniteExact.inst, h2, h3] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h2, h3, Option.some.injEq] at executed
      have t2 := (read d2).symm.trans h2
      have t3 := (read d3).symm.trans h3
      exact passThrough ac (.fpAdd d1 d2 d3) k f frame d1 (holFp64Add .roundTiesToEven x1 x2) source sourcePost target lens
        rfl (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
          StackSemFpRegisterInstructions.instFpRegister, t2, t3]) executed related

/-- Full original evaluate_wInst FPSub case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpSub {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 d3 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpSub d1 d2 d3)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpSub d1 d2 d3) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpSub d1 d2 d3) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpSub d1 d2 d3) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpSub d1 d2 d3)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x1 =>
    cases h3 : WordSemStateFiniteExact.getFpVar d3 source with
    | none => simp [WordSemStateFiniteExact.inst, h2, h3] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h2, h3, Option.some.injEq] at executed
      have t2 := (read d2).symm.trans h2
      have t3 := (read d3).symm.trans h3
      exact passThrough ac (.fpSub d1 d2 d3) k f frame d1 (holFp64Sub .roundTiesToEven x1 x2) source sourcePost target lens
        rfl (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
          StackSemFpRegisterInstructions.instFpRegister, t2, t3]) executed related

/-- Full original evaluate_wInst FPMul case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpMul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 d3 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpMul d1 d2 d3)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpMul d1 d2 d3) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpMul d1 d2 d3) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpMul d1 d2 d3) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpMul d1 d2 d3)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x1 =>
    cases h3 : WordSemStateFiniteExact.getFpVar d3 source with
    | none => simp [WordSemStateFiniteExact.inst, h2, h3] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h2, h3, Option.some.injEq] at executed
      have t2 := (read d2).symm.trans h2
      have t3 := (read d3).symm.trans h3
      exact passThrough ac (.fpMul d1 d2 d3) k f frame d1 (holFp64Mul .roundTiesToEven x1 x2) source sourcePost target lens
        rfl (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
          StackSemFpRegisterInstructions.instFpRegister, t2, t3]) executed related

/-- Full original evaluate_wInst FPDiv case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; the proof names the reviewed binary64 renderings, so
reals_as_rational_cuts is carried explicitly (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
theorem evaluateWInstFpDiv {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 d3 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpDiv d1 d2 d3)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpDiv d1 d2 d3) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpDiv d1 d2 d3) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpDiv d1 d2 d3) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpDiv d1 d2 d3)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
  | none => simp [WordSemStateFiniteExact.inst, h2] at executed
  | some x1 =>
    cases h3 : WordSemStateFiniteExact.getFpVar d3 source with
    | none => simp [WordSemStateFiniteExact.inst, h2, h3] at executed
    | some x2 =>
      simp only [WordSemStateFiniteExact.inst, h2, h3, Option.some.injEq] at executed
      have t2 := (read d2).symm.trans h2
      have t3 := (read d3).symm.trans h3
      exact passThrough ac (.fpDiv d1 d2 d3) k f frame d1 (holFp64Div .roundTiesToEven x1 x2) source sourcePost target lens
        rfl (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
          StackSemFpRegisterInstructions.instFpRegister, t2, t3]) executed related

/-- Full original evaluate_wInst FPFma case (FP branch 5025-5130, generic
tail): wInst passes the instruction through unchanged. All five original guards
(the integer-register guards are vacuous for this opcode), actual native run,
full stateRel and stack resources. FP reads come from state_rel_get_fp_var and
the update from state_rel_set_fp_var. Canonical maps and word widths are
qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpFma {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (d1 d2 d3 k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpFma d1 d2 d3)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (.fp (.fpFma d1 d2 d3) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpFma d1 d2 d3) : WordLangInst (BitVec width)) <
      2 * frame + 2 * k)
    (_convention : instArgConventionExact (.fp (.fpFma d1 d2 d3) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpFma d1 d2 d3)) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have read := fun n => StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related
  cases h1 : WordSemStateFiniteExact.getFpVar d1 source with
  | none => simp [WordSemStateFiniteExact.inst, h1] at executed
  | some x1 =>
    cases h2 : WordSemStateFiniteExact.getFpVar d2 source with
    | none => simp [WordSemStateFiniteExact.inst, h1, h2] at executed
    | some x2 =>
      cases h3 : WordSemStateFiniteExact.getFpVar d3 source with
      | none => simp [WordSemStateFiniteExact.inst, h1, h2, h3] at executed
      | some x3 =>
        simp only [WordSemStateFiniteExact.inst, h1, h2, h3, Option.some.injEq] at executed
        have t1 := (read d1).symm.trans h1
        have t2 := (read d2).symm.trans h2
        have t3 := (read d3).symm.trans h3
        exact passThrough ac (.fpFma d1 d2 d3) k f frame d1 (fpSemFpfma x1 x2 x3) source sourcePost
          target lens rfl (by simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
            StackSemFpRegisterInstructions.instFpRegister, fpSemFpfma, t1, t2, t3]) executed related

end Flapjack.WordToStackProofs.InstSimulation.FpArith
