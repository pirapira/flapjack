import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegisterZero
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.WordToStackProofs.InstSimulation.CarryOverflow
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

/-- Flapjack proof factoring of HOL's three carry/overflow branches; no
separate HOL datatype or declaration is claimed for this proof index. -/
private inductive FlagKind | carry | addOverflow | subOverflow

/-- Flapjack proof factoring of the original source instruction constructors. -/
private def sourceInstruction {width : Nat} (kind : FlagKind) (d a b flag : Nat) :
    WordLangInst (BitVec width) :=
  match kind with
  | .carry => .arith (.addCarry d a b flag)
  | .addOverflow => .arith (.addOverflow d a b flag)
  | .subOverflow => .arith (.subOverflow d a b flag)

/-- Flapjack proof factoring of the corresponding native instruction constructors. -/
private def targetInstruction {width : Nat} [NeZero width]
    (kind : FlagKind) (d a b flag : Nat) : HolInst width :=
  match kind with
  | .carry => .arith (.addCarry d a b flag)
  | .addOverflow => .arith (.addOverflow d a b flag)
  | .subOverflow => .arith (.subOverflow d a b flag)

/-- Flapjack proof factoring of the original word calculations, preserving
both returned words and the original output update order. -/
private def resultWords {width : Nat} [NeZero width] (kind : FlagKind)
    (a b carry : BitVec width) : BitVec width × BitVec width :=
  match kind with
  | .carry => wordAddCarryHOL a b carry
  | .addOverflow => (a+b, if (a+b).toInt ≠ a.toInt+b.toInt then 1 else 0)
  | .subOverflow => (a-b, if (a-b).toInt ≠ a.toInt-b.toInt then 1 else 0)

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

/-- Flapjack infrastructure: success of an actual original flag instruction
internally derives its word operands and entire source post-state. -/
private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (kind : FlagKind) (destination left right : Nat)
    (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (sourceInstruction kind destination left right 0)
      source = some post) :
    ∃ a b carry : BitVec width,
      WordSemStateFiniteExact.getVar left source = some (.word a) ∧
      WordSemStateFiniteExact.getVar right source = some (.word b) ∧
      (kind = .carry → WordSemStateFiniteExact.getVar 0 source = some (.word carry)) ∧
      post = WordSemStateFiniteExact.setVar 0 (.word (resultWords kind a b carry).2)
        (WordSemStateFiniteExact.setVar destination (.word (resultWords kind a b carry).1) source) := by
  cases kind
  · simp only [sourceInstruction, WordSemStateFiniteExact.inst] at run
    split at run
    next a b c read =>
      obtain ⟨ha,hb,hc⟩ := sourceReadsThree source left right 0 (.word a) (.word b) (.word c) read
      cases run
      exact ⟨a,b,c,ha,hb,(fun _ => hc),rfl⟩
    next => contradiction
  · simp only [sourceInstruction, WordSemStateFiniteExact.inst] at run
    split at run
    next a b read =>
      obtain ⟨ha,hb⟩ := sourceReadsTwo source left right (.word a) (.word b) read
      cases run
      exact ⟨a,b,0,ha,hb,(by intro h; cases h),rfl⟩
    next => contradiction
  · simp only [sourceInstruction, WordSemStateFiniteExact.inst] at run
    split at run
    next a b read =>
      obtain ⟨ha,hb⟩ := sourceReadsTwo source left right (.word a) (.word b) read
      cases run
      exact ⟨a,b,0,ha,hb,(by intro h; cases h),rfl⟩
    next => contradiction

/-- Flapjack infrastructure: actual consecutive Reg1/Reg2 native loads
retain the entire source relation and resource equalities and expose both
operand values. The original load theorems derive every frame bound. -/
theorem loadOperands {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame left right regLeft regRight : Nat)
    (loadsLeft loadsRight : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (a b : WordLocW width)
    (compiledLeft : wReg1 left (k,f,frame) = (loadsLeft,regLeft))
    (compiledRight : wReg2 right (k,f,frame) = (loadsRight,regRight))
    (leftEven : left % 2 = 0) (rightEven : right % 2 = 0)
    (leftRead : WordSemStateFiniteExact.getVar left source = some a)
    (rightRead : WordSemStateFiniteExact.getVar right source = some b)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ loaded : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackLoadNative (loadsLeft++loadsRight) .skip,target) =
        (none,loaded) ∧
      target.clock = loaded.clock ∧ stateRel ac k f frame source loaded lens 0 ∧
      loaded.stack.length = target.stack.length ∧ loaded.stackSpace = target.stackSpace ∧
      StackSemStateOps.getVar regLeft loaded = some a ∧
      StackSemStateOps.getVar regRight loaded = some b := by
  obtain ⟨first,firstRun,firstClock,firstRel,firstLength,firstSpace,_,_,leftNe,leftValue⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame left regLeft loadsLeft source target lens
      a compiledLeft leftEven leftRead related
  obtain ⟨loaded,secondRun,secondClock,_,loadedRel,loadedLength,loadedSpace,preserve,_,rightValue⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame right regRight loadsRight source first lens
      b compiledRight rightEven rightRead firstRel
  refine ⟨loaded,?_,firstClock.trans secondClock,loadedRel,loadedLength.trans firstLength,
    loadedSpace.trans firstSpace,(preserve regLeft leftNe).trans leftValue,rightValue⟩
  rw [wStackLoadAppend,Function.comp_apply,LoadRegister.evaluateWStackLoadSeq,
    StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,firstRun]
  simpa only [StackSemControl.fixClock,←firstClock,Nat.min_self] using secondRun

/-- Flapjack factoring of the three genuine original instruction branches.
Only the original five instruction guards enter this helper. All operand
reads, native prefixes, primitive execution and final relation are derived. -/
private theorem evaluateFamily {width : Nat} [NeZero width] {C F : Type}
    (kind : FlagKind) (ac : AsmConfigExact width) (destination left right flag k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (sourceInstruction kind destination left right flag)
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (sourceInstruction (width := width) kind destination left right flag))
    (bound : maxVarInstHOL (sourceInstruction (width := width) kind destination left right flag) <
      2*frame+2*k)
    (convention : instArgConventionExact (targetInstruction (width := width) kind destination left right flag))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (targetInstruction kind destination left right flag)
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have flagZero : flag = 0 := by
    cases kind <;> simpa [targetInstruction,instArgConventionExact] using convention
  subst flag
  obtain ⟨a,b,carry,leftRead,rightRead,carryRead,sourcePostEq⟩ :=
    sourceSuccess kind destination left right source sourcePost executed
  have evens : destination % 2 = 0 ∧ left % 2 = 0 ∧ right % 2 = 0 := by
    cases kind <;> simpa [sourceInstruction,everyVarInstHOL,isPhyVar,and_assoc] using physical
  have destinationBound : destination < 2*frame+2*k := by
    cases kind <;> simp only [sourceInstruction,maxVarInstHOL] at bound <;> omega
  rcases compiledLeft : wReg1 left (k,f,frame) with ⟨loadsLeft,regLeft⟩
  rcases compiledRight : wReg2 right (k,f,frame) with ⟨loadsRight,regRight⟩
  rcases compiledDestination : wReg1 destination (k,f,frame) with ⟨stores,regDestination⟩
  obtain ⟨loaded,loadRun,loadClock,loadedRel,loadedLength,loadedSpace,leftValue,rightValue⟩ :=
    loadOperands ac k f frame left right regLeft regRight loadsLeft loadsRight source target lens
      (.word a) (.word b) compiledLeft compiledRight evens.2.1 evens.2.2 leftRead rightRead related
  have large : 4 < k := by unfold stateRel at related; tauto
  have carryValue : kind = .carry → loaded.regs.lookup 0 = some (.word carry) := by
    intro kindEq
    exact StateRelGetVar.stateRelGetVarImp' ac k f frame source loaded lens 0 0 (.word carry)
      ⟨loadedRel,carryRead kindEq,rfl,(by simpa using (show 0 < k by omega))⟩
  have leftLookup : loaded.regs.lookup regLeft = some (.word a) := leftValue
  have rightLookup : loaded.regs.lookup regRight = some (.word b) := rightValue
  have primitive :
      StackSemEvaluate.evaluate (.inst (targetInstruction kind regDestination regLeft regRight 0),loaded) =
        (none,StackSemStateOps.setVar 0 (.word (resultWords kind a b carry).2)
          (StackSemStateOps.setVar regDestination (.word (resultWords kind a b carry).1) loaded)) := by
    cases kind
    · simp [targetInstruction,resultWords,wordAddCarryHOL,StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL,StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,
        StackSemStateOps.getVar,leftLookup,rightLookup,carryValue rfl]
    · simp [targetInstruction,resultWords,StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL,StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,
        StackSemStateOps.getVar,leftLookup,rightLookup]
    · simp [targetInstruction,resultWords,StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL,StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,
        StackSemStateOps.getVar,leftLookup,rightLookup]
  obtain ⟨post,storeRun,postRel,postLength,postSpace⟩ :=
    StoreRegisterZero.evaluateWStackStoreWReg1Zero ac destination regDestination k f frame stores
      source loaded lens (.word (resultWords kind a b carry).1) (.word (resultWords kind a b carry).2)
      target.stack.length target.stackSpace compiledDestination evens.1 destinationBound loadedRel
      loadedLength loadedSpace
  have writeRun :
      StackSemEvaluate.evaluate (wRegWrite1Native
        (fun reg => .inst (targetInstruction kind reg regLeft regRight 0)) destination (k,f,frame),loaded) =
        (none,post) := by
    simp only [StoreRegister.evaluateWRegWrite1Seq,compiledDestination]
    rw [StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,primitive]
    simpa only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self] using storeRun
  have programEq : wInstNative (targetInstruction (width := width) kind destination left right 0) (k,f,frame) =
      wStackLoadNative (loadsLeft++loadsRight) (wRegWrite1Native
        (fun reg => .inst (targetInstruction kind reg regLeft regRight 0)) destination (k,f,frame)) := by
    cases kind <;> simp only [targetInstruction,wInstNative,compiledLeft,compiledRight]
  refine ⟨post,?_,?_,postLength,postSpace⟩
  · rw [programEq,LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadRun]
    simpa only [StackSemControl.fixClock,←loadClock,Nat.min_self] using writeRun
  · simpa only [sourcePostEq] using postRel

/-- Full original evaluate_wInst Carry case (4755–4775). All five
original guards and the entire existential execution/relation/resource result
are retained, including arbitrary aliases and spilled operands/destination.
Actual source operands, carry input when needed, two native loads, primitive
execution and paired-zero store are proved internally. The shared positive
word width and generic host/FFI carriers match the typed original capture;
canonical map witnesses qualify exactly the five relation fields. Evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8), not a new agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstCarry {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination left right flag k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.addCarry destination left right flag))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.addCarry destination left right flag) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.addCarry destination left right flag) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (convention : instArgConventionExact (.arith (.addCarry destination left right flag) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.addCarry destination left right flag))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateFamily .carry ac destination left right flag k f frame source sourcePost target lens
    executed physical bound convention related

/-- Full original evaluate_wInst AddOverflow case (4738–4754). All five
original guards and the entire existential execution/relation/resource result
are retained, including arbitrary aliases and spilled operands/destination.
Actual source operands, carry input when needed, two native loads, primitive
execution and paired-zero store are proved internally. The shared positive
word width and generic host/FFI carriers match the typed original capture;
canonical map witnesses qualify exactly the five relation fields. Evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8), not a new agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstAddOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination left right flag k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.addOverflow destination left right flag))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.addOverflow destination left right flag) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.addOverflow destination left right flag) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (convention : instArgConventionExact (.arith (.addOverflow destination left right flag) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.addOverflow destination left right flag))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateFamily .addOverflow ac destination left right flag k f frame source sourcePost target lens
    executed physical bound convention related

/-- Full original evaluate_wInst SubOverflow case (4721–4737). All five
original guards and the entire existential execution/relation/resource result
are retained, including arbitrary aliases and spilled operands/destination.
Actual source operands, carry input when needed, two native loads, primitive
execution and paired-zero store are proved internally. The shared positive
word width and generic host/FFI carriers match the typed original capture;
canonical map witnesses qualify exactly the five relation fields. Evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8), not a new agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstSubOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination left right flag k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.subOverflow destination left right flag))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.subOverflow destination left right flag) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.subOverflow destination left right flag) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (convention : instArgConventionExact (.arith (.subOverflow destination left right flag) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.subOverflow destination left right flag))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateFamily .subOverflow ac destination left right flag k f frame source sourcePost target lens
    executed physical bound convention related

end Flapjack.WordToStackProofs.InstSimulation.CarryOverflow
