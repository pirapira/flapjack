import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveAux
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveAuxReconstruction

namespace Flapjack.WordToStackProofs.MoveAuxSimulation
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.Compiler.Backend.Parmove

/-- Flapjack grouping of all seven literal original evaluate_wMoveAux_seqsem
 guards3130–3150, without any extra scheduler or target execution premise.
 realSources is exactly the SOME-filtered twice-THE source projection; its
 getD0 default is unobservable below the isSome filter. -/
def OriginalGuards {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (moves : List (Option Nat × Option Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width)) : Prop :=
  stateRel ac k f frame source target lens 0 ∧
  (∀ i value, env (some i)=some value ↔ WordSemStateFiniteExact.getVar (2*i) source=some value) ∧
  (∀ value, env none=some value → StackSemStateOps.getVar (k+1) target=some value) ∧
  (WordSemStateFiniteExact.getVars (MoveAuxStep.realSources moves) source).isSome=true ∧
  MoveAuxStep.ScratchReady moves env ∧
  (∀ x y, (x,y) ∈ moves → ∀ a, x=some a ∨ y=some a → a<frame+k) ∧
  ((moves.map Prod.fst).filter Option.isSome).Nodup

/-- Flapjack grouping of the entire original native simulation conclusion and
 its guards. It uses the actual faithful target evaluator and complete source
 state expression; no targetrun, desired relation or success is assumed. -/
def Simulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (moves : List (Option Nat × Option Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width)) : Prop :=
  OriginalGuards ac k f frame lens moves source target env →
  ∃ post : StackSemStateFiniteExact width C F,
    StackSemEvaluate.evaluate
      (wMoveAuxNative (moves.map (Prod.map (formatVar k) (formatVar k))) (k,f,frame),target) = (none,post) ∧
    stateRel ac k f frame (MoveAuxReconstruction.sourcePost moves env source) post lens 0 ∧
    post.stack.length=target.stack.length ∧ post.stackSpace=target.stackSpace

/-- Flapjack original guard descent through the actual native head execution.
This inline proof infrastructure has no separate HOL declaration. -/
theorem headAndTailGuards {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (destination sourceReg : Option Nat) (moves : List (Option Nat × Option Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width))
    (guards : OriginalGuards ac k f frame lens ((destination,sourceReg)::moves) source target env) :
    ∃ value post, env sourceReg=some value ∧
      StackSemEvaluate.evaluate
        (wMoveSingleNative (formatVar k destination,formatVar k sourceReg) (k,f,frame),target)=(none,post) ∧
      OriginalGuards ac k f frame lens moves
        (match destination with | none => source | some y => WordSemStateFiniteExact.setVar (2*y) value source)
        post (updateEnv env destination (env sourceReg)) ∧
      post.stack.length=target.stack.length ∧ post.stackSpace=target.stackSpace := by
  rcases guards with ⟨related,correspondence,scratch,reads,ready,bounds,distinct⟩
  have found := MoveAuxStep.actualHeadRead destination sourceReg moves source env correspondence reads ready
  obtain ⟨value,read⟩ : ∃ value, env sourceReg=some value := by
    cases read : env sourceReg with
    | none => simp [read] at found
    | some value => exact ⟨value,rfl⟩
  have sourceRead : MoveSingle.SourceRead k sourceReg value source target := by
    cases sourceReg with
    | none => exact scratch value read
    | some i => simpa [MoveSingle.SourceRead,Nat.mul_comm] using (correspondence i value).mp read
  have bound : match destination with | some y => y<frame+k | none => True := by
    cases destination with
    | none => trivial
    | some y => exact bounds (some y) sourceReg (by simp) y (Or.inl rfl)
  obtain ⟨post,run,relation,scratchNone,scratchSome,length,space⟩ :=
    MoveSingle.wMoveSingleThm ac k f frame source target lens sourceReg destination value related sourceRead (by cases destination with | none => trivial | some y => exact bound)
  refine ⟨value,post,read,run,?_,length,space⟩
  refine ⟨?_,MoveAuxStep.updatedCorrespondence destination sourceReg source env value correspondence read,?_,
    by cases destination <;> simpa using MoveAuxStep.tailReads _ sourceReg moves source value reads,
    MoveAuxStep.scratchReadyTail destination sourceReg moves env ready found,?_,?_⟩
  · cases destination <;> simpa only [Nat.mul_comm] using relation
  · intro v lookup
    cases destination with
    | none =>
      have same : value=v := by simpa [updateEnv,read] using lookup
      subst v
      exact scratchNone rfl
    | some y =>
      have original : env none=some v := by simpa [updateEnv] using lookup
      rw [scratchSome (by simp)]
      exact scratch v original
  · intro x y member a occurs
    exact bounds x y (List.mem_cons_of_mem _ member) a occurs
  · cases destination with
    | none => simpa using distinct
    | some y =>
      have parts : some y ∉ (moves.map Prod.fst).filter Option.isSome ∧
          ((moves.map Prod.fst).filter Option.isSome).Nodup := by simpa using distinct
      exact parts.2

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

/-- Full original cons induction step, with only the generalized structural tail
IH. The seven guards and complete native existential/state/resource conclusion
are exactly the original cons case3130–3285. Inherited rational-cut assurance
applies only to the evaluator closure. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wMoveAux_seqsem"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem simulationCons {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (destination sourceReg : Option Nat) (moves : List (Option Nat × Option Nat))
    (ih : ∀ (source : WordSemStateFiniteExact width (Nat × C) F)
      (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width)), Simulation ac k f frame lens moves source target env)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width)) :
    Simulation ac k f frame lens ((destination,sourceReg)::moves) source target env := by
  intro guards
  obtain ⟨value,headPost,read,headRun,tailGuards,headLength,headSpace⟩ :=
    headAndTailGuards ac k f frame lens destination sourceReg moves source target env guards
  obtain ⟨post,tailRun,tailRelation,tailLength,tailSpace⟩ := ih _ _ _ tailGuards
  refine ⟨post,?_,?_,tailLength.trans headLength,tailSpace.trans headSpace⟩
  · rw [List.map_cons]
    rw [(MoveAux.wMoveAuxThm _ _ (k,f,frame) target).2]
    simp only [Prod.map]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,headRun]
    exact tailRun
  · have reconstruction := MoveAuxReconstruction.sourceStateReconstruction destination sourceReg moves env source value read guards.2.2.2.2.2.2
    cases destination <;> simpa only [reconstruction] using tailRelation

/-- Complete original list simulation3130–3285. The structural induction
hypothesis is discharged; all original guards and conclusions are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wMoveAux_seqsem"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWMoveAuxSeqsem {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (moves : List (Option Nat × Option Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width)) :
    Simulation ac k f frame lens moves source target env := by
  induction moves generalizing source target env with
  | nil =>
    intro guards
    refine ⟨target,(MoveAux.wMoveAuxThm (.inl 0,.inl 0) [] (k,f,frame) target).1,?_,rfl,rfl⟩
    simpa [MoveAuxReconstruction.sourcePost,MoveAuxReconstruction.destinations,
      WordSemStateFiniteExact.setVars,LoopSemStateFiniteExact.sptAlistInsert] using guards.1
  | cons move moves ih =>
    rcases move with ⟨destination,sourceReg⟩
    exact simulationCons ac k f frame lens destination sourceReg moves ih source target env

end Flapjack.WordToStackProofs.MoveAuxSimulation
