import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.CarryOverflow

namespace Flapjack.WordToStackProofs.InstSimulation.Binary
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

/-- Flapjack factoring of actual source register Binop success, with no
successful-operation or post-state premise beyond the original source run. -/
private theorem sourceSuccessReg {width : Nat} [NeZero width] {C F : Type}
    (op : BinOp) (destination input amount : Nat)
    (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (.arith (.binop op destination input (.reg amount))) source = some post) :
    ∃ a b result : BitVec width,
      WordSemStateFiniteExact.getVar input source = some (.word a) ∧
      WordSemStateFiniteExact.getVar amount source = some (.word b) ∧
      wordOpHOL op [a,b] = some result ∧
      post = WordSemStateFiniteExact.setVar destination (.word result) source := by
  cases ha : WordSemStateFiniteExact.getVar input source with
  | none => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
      WordSemStateFiniteExact.wordExp,theWords,ha] at run
  | some av =>
    cases av with
    | loc l n => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
        WordSemStateFiniteExact.wordExp,theWords,ha] at run
    | word a =>
      cases hb : WordSemStateFiniteExact.getVar amount source with
      | none => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
          WordSemStateFiniteExact.wordExp,theWords,ha,hb] at run
      | some bv =>
        cases bv with
        | loc l n => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
            WordSemStateFiniteExact.wordExp,theWords,ha,hb] at run
        | word b =>
          cases hs : wordOpHOL op [a,b] with
          | none => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
              WordSemStateFiniteExact.wordExp,theWords,ha,hb,hs] at run
          | some result =>
            simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
              WordSemStateFiniteExact.wordExp,theWords,ha,hb,hs,Option.map_some,Option.some.injEq] at run
            exact ⟨a,b,result,rfl,rfl,hs,run.symm⟩

/-- Flapjack factoring of actual source immediate Binop success. -/
private theorem sourceSuccessImm {width : Nat} [NeZero width] {C F : Type}
    (op : BinOp) (destination input : Nat) (amount : BitVec width)
    (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (.arith (.binop op destination input (.imm amount))) source = some post) :
    ∃ a result : BitVec width,
      WordSemStateFiniteExact.getVar input source = some (.word a) ∧
      wordOpHOL op [a,amount] = some result ∧
      post = WordSemStateFiniteExact.setVar destination (.word result) source := by
  cases ha : WordSemStateFiniteExact.getVar input source with
  | none => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
      WordSemStateFiniteExact.wordExp,theWords,ha] at run
  | some av =>
    cases av with
    | loc l n => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
        WordSemStateFiniteExact.wordExp,theWords,ha] at run
    | word a =>
      cases hs : wordOpHOL op [a,amount] with
      | none => simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
          WordSemStateFiniteExact.wordExp,theWords,ha,hs] at run
      | some result =>
        simp [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.assign,
          WordSemStateFiniteExact.wordExp,theWords,ha,hs,Option.map_some,Option.some.injEq] at run
        exact ⟨a,result,rfl,hs,run.symm⟩

/-- Full original evaluate_wInst Binop case4863-4919: all five guards and
full actual native run/stateRel/stack resources. Actual operand reads and
successful word operation are derived internally, retaining arbitrary aliases, spill
locations and positive widths. Canonical maps and word widths are qualified;
evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstBinopReg {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : BinOp) (destination input k f frame : Nat)
    (amount : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.binop op destination input (.reg amount)))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.binop op destination input (.reg amount)) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.binop op destination input (.reg amount)) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (_convention : instArgConventionExact (.arith (.binop op destination input (.reg amount)) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.binop op destination input (.reg amount)))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  obtain ⟨a,b,result,inputRead,amountRead,operationResult,sourcePostEq⟩ :=
    sourceSuccessReg op destination input amount source sourcePost executed
  have evens : destination % 2 = 0 ∧ input % 2 = 0 ∧ amount % 2 = 0 := by
    simpa [everyVarInstHOL,everyVarImmHOL,isPhyVar,and_assoc] using physical
  have destinationBound : destination < 2*frame+2*k := by
    simp only [maxVarInstHOL,max3HOL] at bound
    split at bound <;> split at bound <;> omega
  rcases compiledInput : wReg1 input (k,f,frame) with ⟨loadsInput,regInput⟩
  rcases compiledAmount : wReg2 amount (k,f,frame) with ⟨loadsAmount,regAmount⟩
  rcases compiledDestination : wReg1 destination (k,f,frame) with ⟨stores,regDestination⟩
  obtain ⟨loaded,loadRun,loadClock,loadedRel,loadedLength,loadedSpace,inputValue,amountValue⟩ :=
    CarryOverflow.loadOperands ac k f frame input amount regInput regAmount
      loadsInput loadsAmount source target lens (.word a) (.word b)
      compiledInput compiledAmount evens.2.1 evens.2.2 inputRead amountRead related
  have inputLookup : loaded.regs.lookup regInput = some (.word a) := inputValue
  have amountLookup : loaded.regs.lookup regAmount = some (.word b) := amountValue
  have primitive :
      StackSemEvaluate.evaluate (.inst (.arith (.binop op regDestination regInput (.reg regAmount))),loaded) =
        (none,StackSemStateOps.setVar regDestination (.word result) loaded) := by
    by_cases shortcut : op = .or ∧ regAmount = regInput
    · obtain ⟨rfl,sameRegister⟩ := shortcut
      have sameWord : a = b := by
        rw [sameRegister,inputLookup] at amountLookup
        exact WordLocW.word.inj (Option.some.inj amountLookup)
      subst b
      have resultEq : a = result := by
        change some (a ||| (a ||| 0)) = some result at operationResult
        simpa using operationResult
      subst result
      simp [StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
        StackSemIntegerInstructions.instInteger,inputLookup,sameRegister]
    · simp [StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
        StackSemIntegerInstructions.instInteger,StackSemExpressions.assign,StackSemExpressions.wordExp,
        inputLookup,amountLookup,operationResult,shortcut]
  obtain ⟨post,storeRun,postRel,postLength,postSpace⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac destination regDestination k f frame stores source loaded lens
      (.word result) target.stack.length target.stackSpace compiledDestination evens.1
      destinationBound loadedRel loadedLength loadedSpace
  have writeRun :
      StackSemEvaluate.evaluate (wRegWrite1Native
        (fun reg => .inst (.arith (.binop op reg regInput (.reg regAmount)))) destination (k,f,frame),loaded) =
        (none,post) := by
    simp only [StoreRegister.evaluateWRegWrite1Seq,compiledDestination]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,primitive]
    simpa only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self] using storeRun
  refine ⟨post,?_,?_,postLength,postSpace⟩
  · simp only [wInstNative,compiledInput,compiledAmount]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadRun]
    simpa only [StackSemControl.fixClock,←loadClock,Nat.min_self] using writeRun
  · simpa only [sourcePostEq] using postRel


/-- Full original evaluate_wInst Binop case4863-4919: all five guards and
full actual native run/stateRel/stack resources. Actual operand reads and
successful word operation are derived internally, retaining arbitrary aliases, spill
locations and positive widths. Canonical maps and word widths are qualified;
evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstBinopImm {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : BinOp) (destination input k f frame : Nat)
    (amount : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.binop op destination input (.imm amount)))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.binop op destination input (.imm amount)) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.binop op destination input (.imm amount)) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (_convention : instArgConventionExact (.arith (.binop op destination input (.imm amount)) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.binop op destination input (.imm amount)))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  obtain ⟨a,result,inputRead,operationResult,sourcePostEq⟩ :=
    sourceSuccessImm op destination input amount source sourcePost executed
  have evens : destination % 2 = 0 ∧ input % 2 = 0 := by
    simpa [everyVarInstHOL,everyVarImmHOL,isPhyVar,and_assoc] using physical
  have destinationBound : destination < 2*frame+2*k := by
    simp only [maxVarInstHOL] at bound
    omega
  rcases compiledInput : wReg1 input (k,f,frame) with ⟨loadsInput,regInput⟩
  rcases compiledDestination : wReg1 destination (k,f,frame) with ⟨stores,regDestination⟩
  obtain ⟨loaded,loadRun,loadClock,loadedRel,loadedLength,loadedSpace,_,_,_,inputValue⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame input regInput loadsInput source target lens
      (.word a) compiledInput evens.2 inputRead related
  have inputLookup : loaded.regs.lookup regInput = some (.word a) := inputValue
  have primitive :
      StackSemEvaluate.evaluate (.inst (.arith (.binop op regDestination regInput (.imm amount))),loaded) =
        (none,StackSemStateOps.setVar regDestination (.word result) loaded) := by
    simp [StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger,StackSemExpressions.assign,StackSemExpressions.wordExp,
      inputLookup,operationResult]
  obtain ⟨post,storeRun,postRel,postLength,postSpace⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac destination regDestination k f frame stores source loaded lens
      (.word result) target.stack.length target.stackSpace compiledDestination evens.1
      destinationBound loadedRel loadedLength loadedSpace
  have writeRun :
      StackSemEvaluate.evaluate (wRegWrite1Native
        (fun reg => .inst (.arith (.binop op reg regInput (.imm amount)))) destination (k,f,frame),loaded) =
        (none,post) := by
    simp only [StoreRegister.evaluateWRegWrite1Seq,compiledDestination]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,primitive]
    simpa only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self] using storeRun
  refine ⟨post,?_,?_,postLength,postSpace⟩
  · simp only [wInstNative,compiledInput]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadRun]
    simpa only [StackSemControl.fixClock,←loadClock,Nat.min_self] using writeRun
  · simpa only [sourcePostEq] using postRel


end Flapjack.WordToStackProofs.InstSimulation.Binary
