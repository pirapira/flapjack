import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelMemory
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterOffset
import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.WordToStackProofs.InstSimulation.MemoryStore
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

/-- Flapjack factoring of the original memory updates on their common
fields. Plain Store retains Word or Loc payloads; byte/32-bit stores require
words exactly as their original dispatch. No independently named HOL original. -/
private def storeMemory {width : Nat} [NeZero width] (op : WordMemOp)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (be : Bool) (address : BitVec width) (value : WordLocW width) :
    Option (BitVec width → WordLocW width) :=
  match op with
  | .store => if domain address then
      some (fun key => if key = address then value else memory key) else none
  | .store8 => match value with
      | .word word => memStoreByteAuxExact memory domain be address (word.setWidth 8)
      | .loc _ _ => none
  | .store32 => match value with
      | .word word => memStore32Exact memory domain be address (word.setWidth 32)
      | .loc _ _ => none
  | _ => none

/-- Flapjack factoring of actual source-store success: its actual offset,
payload, memory update and whole source poststate are derived internally. -/
private theorem sourceStore {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (valueRegister base : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width C F)
    (kind : op = .store ∨ op = .store8 ∨ op = .store32)
    (executed : WordSemStateFiniteExact.inst (.mem op valueRegister (.addr base offset)) source =
      some sourcePost) :
    ∃ address value memory,
      WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) = some (.word address) ∧
      WordSemStateFiniteExact.getVar valueRegister source = some value ∧
      storeMemory op source.memory source.mdomain source.be address value = some memory ∧
      {source with memory := memory} = sourcePost := by
  have equation : WordSemStateFiniteExact.inst (.mem op valueRegister (.addr base offset)) source =
      (WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset])).bind
        (fun input => match input with
          | .word address => (WordSemStateFiniteExact.getVar valueRegister source).bind
              (fun value => (storeMemory op source.memory source.mdomain source.be address value).map
                (fun memory => {source with memory := memory}))
          | .loc _ _ => none) := by
    rcases kind with rfl | rfl | rfl
    all_goals
      simp only [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.memStore,storeMemory]
      cases WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) with
      | none => rfl
      | some input =>
        cases input with
        | loc l n => rfl
        | word address =>
          cases WordSemStateFiniteExact.getVar valueRegister source with
          | none => rfl
          | some value =>
            cases value <;> simp only [Option.bind_some,Option.map_none]
            all_goals first | rfl | (split <;> simp_all [Option.map])
  rw [equation] at executed
  cases expression : WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) with
  | none => simp [expression] at executed
  | some input =>
    cases input with
    | loc l n => simp [expression] at executed
    | word address =>
      cases read : WordSemStateFiniteExact.getVar valueRegister source with
      | none => simp [expression,read] at executed
      | some value =>
        cases operation : storeMemory op source.memory source.mdomain source.be address value with
        | none => simp [expression,read,operation] at executed
        | some memory =>
          simp [expression,read,operation] at executed
          exact ⟨address,value,memory,rfl,rfl,operation,executed⟩

/-- Flapjack factoring of the existing native target store dispatch, with
actual expression/payload reads and actual memory update, not a desired premise. -/
private theorem targetStore {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (valueRegister base : Nat) (offset : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (kind : op = .store ∨ op = .store8 ∨ op = .store32) :
    StackSemInst.instHOL (.mem op valueRegister (.addr base offset)) target =
      (StackSemExpressions.wordExp target (.op .add [.var base,.const offset])).bind
        (fun address => (StackSemStateOps.getVar valueRegister target).bind
          (fun value => (storeMemory op target.memory target.mdomain target.be address value).map
            (fun memory => {target with memory := memory}))) := by
  rcases kind with rfl | rfl | rfl
  all_goals
    simp only [StackSemInst.instHOL,StackSemIntegerInstructions.instInteger,
      StackSemStateOps.memStore,storeMemory]
    cases StackSemExpressions.wordExp target (.op .add [.var base,.const offset]) with
    | none => rfl
    | some address =>
      cases StackSemStateOps.getVar valueRegister target with
      | none => rfl
      | some value =>
        cases value <;> simp only [Option.join_some,Option.bind_some,Option.map_none]
        all_goals first | rfl | (split <;> simp_all [Option.map])

/-- Flapjack common proof for the three HOL store cases. The internal selector
is discharged by each public case, whose guards remain exactly the originals. -/
private theorem evaluateStore {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (kind : op = .store ∨ op = .store8 ∨ op = .store32)
    (ac : AsmConfigExact width) (valueRegister base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem op valueRegister (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem op valueRegister (.addr base offset)))
    (_bound : maxVarInstHOL (.mem op valueRegister (.addr base offset)) < 2*frame+2*k)
    (_convention : instArgConventionExact (.mem op valueRegister (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem op valueRegister (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : valueRegister % 2 = 0 ∧ base % 2 = 0 := by
    rcases kind with rfl | rfl | rfl
    all_goals simpa [everyVarInstHOL,isPhyVar] using physical
  obtain ⟨address,value,memory,expression,sourceRead,operation,sourceEq⟩ :=
    sourceStore op valueRegister base offset source sourcePost kind executed
  rcases compiledBase : wReg1 base (k,f,frame) with ⟨loadsBase,addressReg⟩
  obtain ⟨first,runFirst,_,relFirst,lengthFirst,spaceFirst,notScratch,expressionFirst⟩ :=
    LoadRegisterOffset.evaluateWStackLoadWReg1WithConst ac k f frame base addressReg loadsBase
      source target lens offset address ⟨compiledBase,even.2,expression,related⟩
  rcases compiledValue : wReg2 valueRegister (k,f,frame) with ⟨loadsValue,valueReg⟩
  obtain ⟨second,runSecond,_,_,relSecond,lengthSecond,spaceSecond,_,preservesExpression,valueRead⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame valueRegister valueReg loadsValue
      source first lens value compiledValue even.1 sourceRead relFirst
  have expressionSecond := (preservesExpression addressReg offset notScratch).trans expressionFirst
  have sameMemory : second.memory = source.memory := relSecond.2.2.2.2.2.2.2.1
  have sameDomain : second.mdomain = source.mdomain := relSecond.2.2.2.2.2.2.2.2.1
  have sameEndian : second.be = source.be := relSecond.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have primitive : StackSemInst.instHOL (.mem op valueReg (.addr addressReg offset)) second =
      some {second with memory := memory} := by
    rw [targetStore op valueReg addressReg offset second kind,expressionSecond]
    simp only [Option.bind_some,valueRead,sameMemory,sameDomain,sameEndian,operation,Option.map_some]
  refine ⟨{second with memory := memory},?_,
    sourceEq ▸ StateRelMemory.stateRelWithMemory ac k f frame source second lens 0 memory relSecond,
    lengthSecond.trans lengthFirst,spaceSecond.trans spaceFirst⟩
  rcases kind with rfl | rfl | rfl
  all_goals
    simp only [wInstNative,compiledBase,compiledValue,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,runFirst]
    dsimp only
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,runSecond]
    simp only [StackSemEvaluate.evaluate_inst,primitive]

/-- Full original Store case of evaluate_wInst4969–5024. All five
original guards and the actual native run/full stateRel/stack resource conclusion
are retained for arbitrary aliases, physical/spilled operands and address offsets.
Plain Store retains Word or Loc payloads; byte/32-bit cases retain their actual
source word conversion. No target read/run/postmemory premise is assumed.
The evaluators inherit reals_as_rational_cuts, without a new FP agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (valueRegister base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .store valueRegister (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .store valueRegister (.addr base offset)))
    (bound : maxVarInstHOL (.mem .store valueRegister (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .store valueRegister (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .store valueRegister (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateStore .store (Or.inl rfl) ac valueRegister base k f frame offset source sourcePost target lens
    executed physical bound convention related

/-- Full original Store8 case of evaluate_wInst4969–5024. All five
original guards and the actual native run/full stateRel/stack resource conclusion
are retained for arbitrary aliases, physical/spilled operands and address offsets.
Plain Store retains Word or Loc payloads; byte/32-bit cases retain their actual
source word conversion. No target read/run/postmemory premise is assumed.
The evaluators inherit reals_as_rational_cuts, without a new FP agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstStore8 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (valueRegister base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .store8 valueRegister (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .store8 valueRegister (.addr base offset)))
    (bound : maxVarInstHOL (.mem .store8 valueRegister (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .store8 valueRegister (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .store8 valueRegister (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateStore .store8 (Or.inr (Or.inl rfl)) ac valueRegister base k f frame offset source sourcePost target lens
    executed physical bound convention related

/-- Full original Store32 case of evaluate_wInst4969–5024. All five
original guards and the actual native run/full stateRel/stack resource conclusion
are retained for arbitrary aliases, physical/spilled operands and address offsets.
Plain Store retains Word or Loc payloads; byte/32-bit cases retain their actual
source word conversion. No target read/run/postmemory premise is assumed.
The evaluators inherit reals_as_rational_cuts, without a new FP agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstStore32 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (valueRegister base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .store32 valueRegister (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .store32 valueRegister (.addr base offset)))
    (bound : maxVarInstHOL (.mem .store32 valueRegister (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .store32 valueRegister (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .store32 valueRegister (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateStore .store32 (Or.inr (Or.inr rfl)) ac valueRegister base k f frame offset source sourcePost target lens
    executed physical bound convention related

end Flapjack.WordToStackProofs.InstSimulation.MemoryStore
