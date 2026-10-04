import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegister
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.WordToStackProofs.InstSimulation.LongArithmetic
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

/-- Flapjack infrastructure: the actual successful two-name source read
fixes both values; no desired environment relation is assumed. -/
private theorem sourceReadsTwo {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (a b : Nat) (av bv : WordLocW width)
    (read : WordSemStateFiniteExact.getVars [a,b] source = some [av,bv]) :
    WordSemStateFiniteExact.getVar a source = some av ∧
      WordSemStateFiniteExact.getVar b source = some bv := by
  cases ha : WordSemStateFiniteExact.getVar a source <;>
    cases hb : WordSemStateFiniteExact.getVar b source <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- Flapjack infrastructure: the actual three-name source read fixes every
value, including the original carry input. -/
private theorem sourceReadsThree {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (a b c : Nat) (av bv cv : WordLocW width)
    (read : WordSemStateFiniteExact.getVars [a,b,c] source = some [av,bv,cv]) :
    WordSemStateFiniteExact.getVar a source = some av ∧
      WordSemStateFiniteExact.getVar b source = some bv ∧
      WordSemStateFiniteExact.getVar c source = some cv := by
  cases ha : WordSemStateFiniteExact.getVar a source <;>
    cases hb : WordSemStateFiniteExact.getVar b source <;>
    cases hc : WordSemStateFiniteExact.getVar c source <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- Flapjack infrastructure: successful literal LongMul fixes both original
word operands and the entire two-register source post-state. -/
private theorem longMulSource {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (.arith (.longMul 6 0 0 4)) source = some post) :
    ∃ a b : BitVec width,
      WordSemStateFiniteExact.getVar 0 source = some (.word a) ∧
      WordSemStateFiniteExact.getVar 4 source = some (.word b) ∧
      post = WordSemStateFiniteExact.setVar 0 (.word (BitVec.ofNat width (a.toNat*b.toNat)))
        (WordSemStateFiniteExact.setVar 6
          (.word (BitVec.ofNat width (a.toNat*b.toNat / 2^width))) source) := by
  simp only [WordSemStateFiniteExact.inst] at run
  split at run
  next a b read =>
    obtain ⟨ha,hb⟩ := sourceReadsTwo source 0 4 (.word a) (.word b) read
    cases run
    exact ⟨a,b,ha,hb,rfl⟩
  next => contradiction

/-- Flapjack infrastructure: successful literal LongDiv fixes all three
original word operands, original quotient guards and the whole source post. -/
private theorem longDivSource {width : Nat} [NeZero width] {C F : Type}
    (divisorRegister : Nat) (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (.arith (.longDiv 0 6 6 0 divisorRegister)) source = some post) :
    ∃ high low divisor : BitVec width,
      WordSemStateFiniteExact.getVar 6 source = some (.word high) ∧
      WordSemStateFiniteExact.getVar 0 source = some (.word low) ∧
      WordSemStateFiniteExact.getVar divisorRegister source = some (.word divisor) ∧
      divisor.toNat ≠ 0 ∧ (high.toNat * 2^width + low.toNat) / divisor.toNat < 2^width ∧
      post = WordSemStateFiniteExact.setVar 0
        (.word (BitVec.ofNat width ((high.toNat * 2^width + low.toNat) / divisor.toNat)))
        (WordSemStateFiniteExact.setVar 6
          (.word (BitVec.ofNat width ((high.toNat * 2^width + low.toNat) % divisor.toNat))) source) := by
  simp only [WordSemStateFiniteExact.inst] at run
  split at run
  next high low divisor read =>
    obtain ⟨hh,hl,hd⟩ := sourceReadsThree source 6 0 divisorRegister
      (.word high) (.word low) (.word divisor) read
    split at run
    next guarded =>
      cases run
      exact ⟨high,low,divisor,hh,hl,hd,guarded.1,guarded.2,rfl⟩
    next => contradiction
  next => contradiction

/-- Full original evaluate_wInst LongMul case (4790–4800), including all
five original guards and complete existential run/relation/resource result.
The original argument convention fixes all four registers; source success
fixes both actual word operands. Both native updates and the entire source
post-state relation are derived, with no target-run/postrelation premise.
Canonical maps and shared positive word width are explicitly qualified;
evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstLongMul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (highDestination lowDestination left right k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.longMul highDestination lowDestination left right))
      source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar
      (.arith (.longMul highDestination lowDestination left right) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL
      (.arith (.longMul highDestination lowDestination left right) : WordLangInst (BitVec width)) < 2*frame+2*k)
    (convention : instArgConventionExact
      (.arith (.longMul highDestination lowDestination left right) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.longMul highDestination lowDestination left right))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have registers : highDestination = 6 ∧ lowDestination = 0 ∧ left = 0 ∧ right = 4 := by
    simpa [instArgConventionExact,and_assoc] using convention
  obtain ⟨rfl,rfl,rfl,rfl⟩ := registers
  obtain ⟨a,b,leftRead,rightRead,sourcePostEq⟩ := longMulSource source sourcePost executed
  have large : 4 < k := by unfold stateRel at related; tauto
  have leftLookup : target.regs.lookup 0 = some (.word a) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 0 (.word a)
      ⟨related,leftRead,rfl,(by simpa using (show 0 < k by omega))⟩
  have rightLookup : target.regs.lookup 2 = some (.word b) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 4 (.word b)
      ⟨related,rightRead,rfl,(by simpa using (show 2 < k by omega))⟩
  let high := BitVec.ofNat width (a.toNat*b.toNat / 2^width)
  let low := BitVec.ofNat width (a.toNat*b.toNat)
  let post := StackSemStateOps.setVar 0 (.word low) (StackSemStateOps.setVar 3 (.word high) target)
  refine ⟨post,?_,?_,rfl,rfl⟩
  · simp [post,high,low,wInstNative,StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,StackSemStateOps.getVar,
      leftLookup,rightLookup]
  · have highRel := StateRelRegisterUpdate.stateRelSetVar 3 (.word high) related (by omega)
    have lowRel := StateRelRegisterUpdate.stateRelSetVar 0 (.word low) highRel (by omega)
    simpa [post,high,low,sourcePostEq] using lowRel

/-- Full original evaluate_wInst LongDiv case (4776–4789), preserving all
five original guards, actual native load and primitive run, whole post-state
relation and both stack-resource equations. Source success internally derives
the original divisor/quotient guards; the native Reg1 load derives frame bounds.
No target-run, postrelation or extra success premise is supplied. Canonical maps
and shared positive word width are qualified; evaluators inherit
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstLongDiv {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (quotientDestination remainderDestination high low divisorRegister k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst
      (.arith (.longDiv quotientDestination remainderDestination high low divisorRegister)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.longDiv quotientDestination remainderDestination high low divisorRegister) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL
      (.arith (.longDiv quotientDestination remainderDestination high low divisorRegister) : WordLangInst (BitVec width)) <
        2*frame+2*k)
    (convention : instArgConventionExact
      (.arith (.longDiv quotientDestination remainderDestination high low divisorRegister) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate
        (wInstNative (.arith (.longDiv quotientDestination remainderDestination high low divisorRegister))
          (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have registers : quotientDestination = 0 ∧ remainderDestination = 6 ∧ high = 6 ∧ low = 0 := by
    simpa [instArgConventionExact,and_assoc] using convention
  obtain ⟨rfl,rfl,rfl,rfl⟩ := registers
  have divisorEven : divisorRegister % 2 = 0 := by
    simpa [everyVarInstHOL,isPhyVar] using physical
  obtain ⟨high,low,divisor,highRead,lowRead,divisorRead,nonzero,quotientBound,sourcePostEq⟩ :=
    longDivSource divisorRegister source sourcePost executed
  rcases compiled : wReg1 divisorRegister (k,f,frame) with ⟨loads,register⟩
  obtain ⟨loaded,loadRun,loadClock,loadedRel,loadedLength,loadedSpace,_,_,_,divisorValue⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame divisorRegister register loads source target lens
      (.word divisor) compiled divisorEven divisorRead related
  have large : 4 < k := by unfold stateRel at related; tauto
  have highLookup : loaded.regs.lookup 3 = some (.word high) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source loaded lens 0 6 (.word high)
      ⟨loadedRel,highRead,rfl,(by simpa using (show 3 < k by omega))⟩
  have lowLookup : loaded.regs.lookup 0 = some (.word low) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source loaded lens 0 0 (.word low)
      ⟨loadedRel,lowRead,rfl,(by simpa using (show 0 < k by omega))⟩
  have divisorLookup : loaded.regs.lookup register = some (.word divisor) := divisorValue
  let numerator := high.toNat*2^width+low.toNat
  let quotient := BitVec.ofNat width (numerator / divisor.toNat)
  let remainder := BitVec.ofNat width (numerator % divisor.toNat)
  let post := StackSemStateOps.setVar 0 (.word quotient)
    (StackSemStateOps.setVar 3 (.word remainder) loaded)
  have primitive : StackSemEvaluate.evaluate (.inst (.arith (.longDiv 0 3 3 0 register)),loaded) =
      (none,post) := by
    simp [post,numerator,quotient,remainder,StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,StackSemStateOps.getVar,
      highLookup,lowLookup,divisorLookup,nonzero,quotientBound]
  refine ⟨post,?_,?_,loadedLength,loadedSpace⟩
  · simp only [wInstNative,compiled]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadRun]
    simpa only [StackSemControl.fixClock,←loadClock,Nat.min_self] using primitive
  · have remainderRel := StateRelRegisterUpdate.stateRelSetVar 3 (.word remainder) loadedRel (by omega)
    have quotientRel := StateRelRegisterUpdate.stateRelSetVar 0 (.word quotient) remainderRel (by omega)
    simpa [post,numerator,quotient,remainder,sourcePostEq] using quotientRel

end Flapjack.WordToStackProofs.InstSimulation.LongArithmetic
