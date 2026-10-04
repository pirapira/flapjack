import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterOffset
import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.WordToStackProofs.InstSimulation.MemoryLoad
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

/-- Flapjack factoring of the three original memory reads on their common
memory/domain/endian fields; no independently named HOL original. -/
private def loadValue {width : Nat} [NeZero width] (op : WordMemOp)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (be : Bool) (address : BitVec width) : Option (WordLocW width) :=
  match op with
  | .load => if domain address then some (memory address) else none
  | .load8 => (memLoadByteAuxExact memory domain be address).map
      (fun value => .word (value.setWidth width))
  | .load32 => (memLoad32Exact memory domain be address).map
      (fun value => .word (value.setWidth width))
  | _ => none

/-- Flapjack factoring of actual source-load success, including its source
poststate. The internal opcode guard selects exactly the three original cases. -/
private theorem sourceLoad {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (destination base : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width C F)
    (kind : op = .load ∨ op = .load8 ∨ op = .load32)
    (executed : WordSemStateFiniteExact.inst (.mem op destination (.addr base offset)) source =
      some sourcePost) :
    ∃ address value,
      WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) = some (.word address) ∧
      loadValue op source.memory source.mdomain source.be address = some value ∧
      WordSemStateFiniteExact.setVar destination value source = sourcePost := by
  have equation : WordSemStateFiniteExact.inst (.mem op destination (.addr base offset)) source =
      (WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset])).bind
        (fun input => match input with
          | .word address => (loadValue op source.memory source.mdomain source.be address).map
              (fun value => WordSemStateFiniteExact.setVar destination value source)
          | .loc _ _ => none) := by
    rcases kind with rfl | rfl | rfl
    all_goals
      simp only [WordSemStateFiniteExact.inst,WordSemStateFiniteExact.memLoad,loadValue]
      cases WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) with
      | none => rfl
      | some input =>
        cases input <;> try rfl
        simp only [Option.bind_some,Option.map_map]
        split <;> simp_all [Option.map]
  rw [equation] at executed
  cases expression : WordSemStateFiniteExact.wordExp source (.op .add [.var base,.const offset]) with
  | none => simp [expression] at executed
  | some input =>
    cases input with
    | loc l n => simp [expression] at executed
    | word address =>
      cases read : loadValue op source.memory source.mdomain source.be address with
      | none => simp [expression,read] at executed
      | some value =>
        simp [expression,read] at executed
        exact ⟨address,value,rfl,read,executed⟩

/-- Flapjack factoring of actual native target instruction dispatch. The
result is an equation of the existing faithful operation, not a premise. -/
private theorem targetLoad {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (destination base : Nat) (offset : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (kind : op = .load ∨ op = .load8 ∨ op = .load32) :
    StackSemInst.instHOL (.mem op destination (.addr base offset)) target =
      (StackSemExpressions.wordExp target (.op .add [.var base,.const offset])).bind
        (fun address => (loadValue op target.memory target.mdomain target.be address).map
          (fun value => StackSemStateOps.setVar destination value target)) := by
  rcases kind with rfl | rfl | rfl
  all_goals
    simp only [StackSemInst.instHOL,StackSemIntegerInstructions.instInteger,
      StackSemStateOps.memLoad,loadValue]
    cases StackSemExpressions.wordExp target (.op .add [.var base,.const offset]) <;>
      simp only [Option.join_some,Option.bind_none,Option.bind_some,Option.map_map]
    all_goals first | rfl | (split <;> simp_all [Option.map])

/-- Flapjack common proof for exactly the three HOL load cases. Its internal
opcode selector is discharged by each public theorem and adds no public guard. -/
private theorem evaluateLoad {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (kind : op = .load ∨ op = .load8 ∨ op = .load32)
    (ac : AsmConfigExact width) (destination base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem op destination (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem op destination (.addr base offset)))
    (bound : maxVarInstHOL (.mem op destination (.addr base offset)) < 2*frame+2*k)
    (_convention : instArgConventionExact (.mem op destination (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem op destination (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : destination % 2 = 0 ∧ base % 2 = 0 := by
    rcases kind with rfl | rfl | rfl
    all_goals simpa [everyVarInstHOL,isPhyVar] using physical
  have bounds : max base destination < 2*frame+2*k := by
    rcases kind with rfl | rfl | rfl
    all_goals simpa [maxVarInstHOL] using bound
  have destinationBound : destination < 2*frame+2*k := by omega
  obtain ⟨address,value,expression,read,sourceEq⟩ :=
    sourceLoad op destination base offset source sourcePost kind executed
  rcases compiledBase : wReg1 base (k,f,frame) with ⟨loads,addressReg⟩
  obtain ⟨loadedState,loadedStateRun,_,loadedStateRel,lengthEq,spaceEq,_,targetExpression⟩ :=
    LoadRegisterOffset.evaluateWStackLoadWReg1WithConst ac k f frame base addressReg loads
      source target lens offset address ⟨compiledBase,even.2,expression,related⟩
  have sameMemory : loadedState.memory = source.memory := loadedStateRel.2.2.2.2.2.2.2.1
  have sameDomain : loadedState.mdomain = source.mdomain := loadedStateRel.2.2.2.2.2.2.2.2.1
  have sameEndian : loadedState.be = source.be := loadedStateRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases compiledDestination : wReg1 destination (k,f,frame) with ⟨stores,destinationReg⟩
  have primitive : StackSemInst.instHOL (.mem op destinationReg (.addr addressReg offset)) loadedState =
      some (StackSemStateOps.setVar destinationReg value loadedState) := by
    rw [targetLoad op destinationReg addressReg offset loadedState kind,targetExpression]
    simp only [Option.bind_some,sameMemory,sameDomain,sameEndian,read,Option.map_some]
  obtain ⟨post,storeRun,postRel,lengthPost,spacePost⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac destination destinationReg k f frame stores
      source loadedState lens value target.stack.length target.stackSpace
      compiledDestination even.1 destinationBound loadedStateRel lengthEq spaceEq
  refine ⟨post,?_,sourceEq ▸ postRel,lengthPost,spacePost⟩
  rcases kind with rfl | rfl | rfl
  all_goals
    simp only [wInstNative,compiledBase]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,loadedStateRun]
    simp only [StoreRegister.evaluateWRegWrite1Seq,compiledDestination]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_inst,primitive]
    exact storeRun

/-- Full original Load case of evaluate_wInst4919–4969. All five
original guards and every actual native run/full stateRel/stack resource result
are retained, including destination/base aliases and physical/spilled variables.
No target read/run/postmemory premise is assumed. The evaluators inherit
reals_as_rational_cuts; no independent numerical FP agreement is claimed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstLoad {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .load destination (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .load destination (.addr base offset)))
    (bound : maxVarInstHOL (.mem .load destination (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .load destination (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .load destination (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateLoad .load (Or.inl rfl) ac destination base k f frame offset source sourcePost target lens
    executed physical bound convention related

/-- Full original Load8 case of evaluate_wInst4919–4969. All five
original guards and every actual native run/full stateRel/stack resource result
are retained, including destination/base aliases and physical/spilled variables.
No target read/run/postmemory premise is assumed. The evaluators inherit
reals_as_rational_cuts; no independent numerical FP agreement is claimed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstLoad8 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .load8 destination (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .load8 destination (.addr base offset)))
    (bound : maxVarInstHOL (.mem .load8 destination (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .load8 destination (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .load8 destination (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateLoad .load8 (Or.inr (Or.inl rfl)) ac destination base k f frame offset source sourcePost target lens
    executed physical bound convention related

/-- Full original Load32 case of evaluate_wInst4919–4969. All five
original guards and every actual native run/full stateRel/stack resource result
are retained, including destination/base aliases and physical/spilled variables.
No target read/run/postmemory premise is assumed. The evaluators inherit
reals_as_rational_cuts; no independent numerical FP agreement is claimed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstLoad32 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem .load32 destination (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem .load32 destination (.addr base offset)))
    (bound : maxVarInstHOL (.mem .load32 destination (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem .load32 destination (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem .load32 destination (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace :=
  evaluateLoad .load32 (Or.inr (Or.inr rfl)) ac destination base k f frame offset source sourcePost target lens
    executed physical bound convention related

end Flapjack.WordToStackProofs.InstSimulation.MemoryLoad
