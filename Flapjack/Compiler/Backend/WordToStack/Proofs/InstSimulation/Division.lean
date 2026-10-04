import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.CarryOverflow

namespace Flapjack.WordToStackProofs.InstSimulation.Division
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

/-- Flapjack infrastructure: equality of the two Lean sign-case renderings
of signed division, including zero divisors. This compares native definitions
and has no separate HOL theorem original or cross-language agreement claim. -/
private theorem wordQuotEqSdiv {width : Nat} (a b : BitVec width) :
    StackSemIntegerInstructions.wordQuot a b = a.sdiv b := by
  cases ha : a.msb <;> cases hb : b.msb <;>
    simp [StackSemIntegerInstructions.wordQuot,BitVec.sdiv,ha,hb]

/-- Flapjack infrastructure: actual source division success determines both
word operands, its original nonzero divisor and the entire source post-state. -/
private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (destination numerator denominator : Nat)
    (source post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.inst (.arith (.div destination numerator denominator)) source = some post) :
    ∃ a b : BitVec width,
      WordSemStateFiniteExact.getVar numerator source = some (.word a) ∧
      WordSemStateFiniteExact.getVar denominator source = some (.word b) ∧ b ≠ 0 ∧
      post = WordSemStateFiniteExact.setVar destination (.word (a.sdiv b)) source := by
  simp only [WordSemStateFiniteExact.inst] at run
  split at run
  next b a read =>
    obtain ⟨hb,ha⟩ := sourceReadsTwo source denominator numerator (.word b) (.word a) read
    split at run
    next nonzero =>
      cases run
      exact ⟨a,b,ha,hb,nonzero,rfl⟩
    next => contradiction
  next => contradiction

/-- Full original evaluate_wInst Div case (4801–4819). All five guards and
the complete existential actual native run/full source-post-target-post relation
and stack resource equalities are retained. Actual word operands and nonzero
divisor, both native operand loads, quotient calculation and register/spill
write are derived internally, including arbitrary aliases and all positive widths.
Canonical maps are qualified; source/target/result word width is shared and
host/FFI types remain independent. Evaluators inherit reals_as_rational_cuts
(SOUNDNESS item 8), without a new agreement assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstDiv {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination numerator denominator k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith (.div destination numerator denominator))
      source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith (.div destination numerator denominator) : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith (.div destination numerator denominator) : WordLangInst (BitVec width)) <
      2*frame+2*k)
    (_convention : instArgConventionExact (.arith (.div destination numerator denominator) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith (.div destination numerator denominator))
        (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  obtain ⟨a,b,numeratorRead,denominatorRead,nonzero,sourcePostEq⟩ :=
    sourceSuccess destination numerator denominator source sourcePost executed
  have evens : destination % 2 = 0 ∧ numerator % 2 = 0 ∧ denominator % 2 = 0 := by
    simpa [everyVarInstHOL,isPhyVar,and_assoc] using physical
  have destinationBound : destination < 2*frame+2*k := by
    simp only [maxVarInstHOL,max3HOL] at bound
    split at bound <;> split at bound <;> omega
  rcases compiledNumerator : wReg1 numerator (k,f,frame) with ⟨loadsNumerator,regNumerator⟩
  rcases compiledDenominator : wReg2 denominator (k,f,frame) with ⟨loadsDenominator,regDenominator⟩
  rcases compiledDestination : wReg1 destination (k,f,frame) with ⟨stores,regDestination⟩
  obtain ⟨loaded,loadRun,loadClock,loadedRel,loadedLength,loadedSpace,numeratorValue,denominatorValue⟩ :=
    CarryOverflow.loadOperands ac k f frame numerator denominator regNumerator regDenominator
      loadsNumerator loadsDenominator source target lens (.word a) (.word b)
      compiledNumerator compiledDenominator evens.2.1 evens.2.2 numeratorRead denominatorRead related
  have numeratorLookup : loaded.regs.lookup regNumerator = some (.word a) := numeratorValue
  have denominatorLookup : loaded.regs.lookup regDenominator = some (.word b) := denominatorValue
  have nonzeroLiteral : b ≠ (0#width) := by simpa using nonzero
  have primitive :
      StackSemEvaluate.evaluate (.inst (.arith (.div regDestination regNumerator regDenominator)),loaded) =
        (none,StackSemStateOps.setVar regDestination (.word (a.sdiv b)) loaded) := by
    simp [StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger,StackSemStateOps.getVars,StackSemStateOps.getVar,
      numeratorLookup,denominatorLookup,nonzeroLiteral,wordQuotEqSdiv]
  obtain ⟨post,storeRun,postRel,postLength,postSpace⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac destination regDestination k f frame stores source loaded lens
      (.word (a.sdiv b)) target.stack.length target.stackSpace compiledDestination evens.1
      destinationBound loadedRel loadedLength loadedSpace
  have writeRun :
      StackSemEvaluate.evaluate (wRegWrite1Native
        (fun reg => .inst (.arith (.div reg regNumerator regDenominator))) destination (k,f,frame),loaded) =
        (none,post) := by
    simp only [StoreRegister.evaluateWRegWrite1Seq,compiledDestination]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,primitive]
    simpa only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self] using storeRun
  refine ⟨post,?_,?_,postLength,postSpace⟩
  · simp only [wInstNative,compiledNumerator,compiledDenominator]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadRun]
    simpa only [StackSemControl.fixClock,←loadClock,Nat.min_self] using writeRun
  · simpa only [sourcePostEq] using postRel

end Flapjack.WordToStackProofs.InstSimulation.Division
