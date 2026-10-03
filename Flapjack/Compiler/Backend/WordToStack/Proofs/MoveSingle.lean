import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.WordToStackProofs.MoveSingle
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Flapjack extraction of the actual optional source read in the original
move theorem; no separate HOL declaration names this grouping. -/
def SourceRead {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (x : Option Nat) (value : WordLocW width)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) : Prop :=
  match x with
  | none => StackSemStateOps.getVar (k+1) target = some value
  | some x => WordSemStateFiniteExact.getVar (x*2) source = some value

/-- Flapjack source-relation projection onto the actual bounded spill read.
It uses getElem? and never relies on a total out-of-range list accessor. -/
private theorem spillRead {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame x : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {value : WordLocW width}
    (related : stateRel ac k f frame source target lens 0)
    (read : WordSemStateFiniteExact.getVar (x*2) source = some value) (spilled : ¬x<k) :
    target.stack[target.stackSpace+(f-1-(x-k))]? = some value := by
  have placement := StateRelGetVar.stateRel_locals related (x*2) value read
  have half : x*2/2=x := by omega
  rw [half, if_neg spilled] at placement
  rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at placement
  split at placement
  · exact placement.2.1
  · simp_all

/-- Flapjack computation of the original register/stack source alternatives
into any destination register, including scratch and location-valued moves. -/
private theorem readToRegister {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (x : Option Nat) (destination : Nat) (value : WordLocW width)
    (related : stateRel ac k f frame source target lens 0)
    (read : SourceRead k x value source target) :
    StackSemEvaluate.evaluate (wMoveSingleNative (.inl destination,formatVar k x) (k,f,frame),target) =
      (none,StackSemStateOps.setVar destination value target) := by
  cases x with
  | none =>
    simp only [SourceRead] at read
    simp [formatVar,wMoveSingleNative,StackSemEvaluate.evaluate_inst,
      StackSemInst.instHOL,StackSemIntegerInstructions.instInteger_or_self,
      StackSemStateOps.getVar] at read ⊢
    rw [read]
  | some x =>
    simp only [SourceRead] at read
    by_cases physical : x<k
    · have registerRead := StateRelGetVar.stateRelGetVarImp ac k f frame source target lens 0 x value
        ⟨related,by simpa [Nat.mul_comm] using read,physical⟩
      simp [formatVar,physical,wMoveSingleNative,StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL,StackSemIntegerInstructions.instInteger_or_self,registerRead]
    · have slot := spillRead related read physical
      obtain ⟨bound,contents⟩ := List.getElem?_eq_some_iff.mp slot
      have useStack : target.useStack=true := related.2.2.2.2.1
      simp [formatVar,physical,wMoveSingleNative,StackSemEvaluate.evaluate_stackLoad,
        useStack,bound,contents]

/-- Flapjack derivation of the original destination frame bound; the original
state relation supplies the complete frame shape and available stack. -/
private theorem destinationBound {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame y : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (related : stateRel ac k f frame source target lens 0)
    (spilled : ¬y<k) (bound : y<frame+k) :
    target.stackSpace+(f-1-(y-k)) < target.stack.length ∧
      f-1-(y-k)=f+k-(y+1) := by
  have shape : if frame=0 then f=0 else f=frame+1 :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have resource : target.stackSpace+f ≤ target.stack.length :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split at shape <;> omega

/-- Flapjack calculation of a real stack store and its full source-local
update relation. Its read and bounds are established by the original guards. -/
private theorem storeToSlot {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame y : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (register : Nat) (value : WordLocW width)
    (related : stateRel ac k f frame source target lens 0)
    (spilled : ¬y<k) (bound : y<frame+k)
    (read : StackSemStateOps.getVar register target = some value) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (.stackStore register (f-1-(y-k)),target) = (none,post) ∧
      stateRel ac k f frame (WordSemStateFiniteExact.setVar (y*2) value source) post lens 0 ∧
      StackSemStateOps.getVar (k+1) post = StackSemStateOps.getVar (k+1) target ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  obtain ⟨slotBound,slotEq⟩ := destinationBound related spilled bound
  let post := {target with stack := target.stack.set (target.stackSpace+(f-1-(y-k))) value}
  refine ⟨post,?_,?_,rfl,by simp [post],rfl⟩
  · have useStack : target.useStack=true := related.2.2.2.2.1
    simp [StackSemEvaluate.evaluate_stackStore,useStack,Nat.not_le.mpr slotBound,read,post]
  · simpa [post,slotEq,Nat.mul_comm] using
      StateRelRegisterUpdate.wordToStackStateRelSetVar2 y value target.stack target.stackSpace
        related spilled bound rfl rfl

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

/-- Full original single-move simulation2995–3109, including both temporary
observations and both target stack preservation conclusions. Inherited
reals_as_rational_cuts applies to the evaluator closure, with no new FP
correspondence claim. All optional
source/destination and register/spill alternatives remain arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveSingle_thm"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wMoveSingleThm {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (x y : Option Nat) (value : WordLocW width)
    (related : stateRel ac k f frame source target lens 0)
    (read : SourceRead k x value source target)
    (bound : match y with | some y => y<frame+k | none => True) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wMoveSingleNative (formatVar k y,formatVar k x) (k,f,frame),target) =
        (none,post) ∧
      stateRel ac k f frame (match y with | none => source | some y => WordSemStateFiniteExact.setVar (y*2) value source)
        post lens 0 ∧
      (y=none → StackSemStateOps.getVar (k+1) post=some value) ∧
      (y≠none → StackSemStateOps.getVar (k+1) post=StackSemStateOps.getVar (k+1) target) ∧
      post.stack.length=target.stack.length ∧ post.stackSpace=target.stackSpace := by
  cases y with
  | none =>
    refine ⟨StackSemStateOps.setVar (k+1) value target,?_,?_,?_,by simp,rfl,rfl⟩
    · exact readToRegister x (k+1) value related read
    · exact CallDest.stateRel_setVar_of_ge (k+1) (by omega) value related
    · intro _; simp [StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL]
  | some y =>
    by_cases physical : y<k
    · refine ⟨StackSemStateOps.setVar y value target,?_,?_,by simp,?_,rfl,rfl⟩
      · simpa only [formatVar,if_pos physical] using readToRegister x y value related read
      · simpa only [Nat.mul_comm] using StateRelRegisterUpdate.stateRelSetVar y value related physical
      · intro _
        simp [StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL,
          show k+1≠y by omega]
    · cases x with
      | none =>
        obtain ⟨post,run,relation,scratch,len,space⟩ := storeToSlot (k+1) value related physical bound read
        refine ⟨post,?_,relation,by simp,fun _ => scratch,len,space⟩
        simpa only [formatVar,if_neg physical,wMoveSingleNative] using run
      | some x =>
        by_cases sourcePhysical : x<k
        · have actualRead := StateRelGetVar.stateRelGetVarImp ac k f frame source target lens 0 x value
            ⟨related,by simpa [SourceRead,Nat.mul_comm] using read,sourcePhysical⟩
          obtain ⟨post,run,relation,scratch,len,space⟩ := storeToSlot x value related physical bound actualRead
          refine ⟨post,?_,relation,by simp,fun _ => scratch,len,space⟩
          simpa only [formatVar,if_neg physical,if_pos sourcePhysical,wMoveSingleNative] using run
        · let loaded := StackSemStateOps.setVar k value target
          have loadedRel := CallDest.stateRel_setVar_of_ge k (Nat.le_refl _) value related
          have loadedRead : StackSemStateOps.getVar k loaded=some value := by
            simp [loaded,StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL]
          obtain ⟨post,run,relation,scratch,len,space⟩ := storeToSlot k value loadedRel physical bound loadedRead
          refine ⟨post,?_,relation,by simp,?_,len,space⟩
          · have loadRun := readToRegister (some x) k value related read
            simp only [formatVar,if_neg sourcePhysical,wMoveSingleNative] at loadRun
            simp only [formatVar,if_neg physical,if_neg sourcePhysical,wMoveSingleNative,
              StackSemEvaluate.evaluate_seq,loadRun]
            simpa [StackSemControl.fixClock,StackSemStateOps.setVar,loaded] using run
          · intro _
            rw [scratch]
            simp [StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL]

end Flapjack.WordToStackProofs.MoveSingle
