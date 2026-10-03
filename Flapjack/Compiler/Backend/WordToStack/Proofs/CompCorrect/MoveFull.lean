import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveSourceState
namespace Flapjack.WordToStackProofs.CompCorrect.MoveFull
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
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

/-- Full original Move constructor6132–6313 under the unchanged simulation
motive. Source success, actual native scheduling and complete source equality
are derived internally. No induction hypothesis is needed for this leaf.
Evaluator closure inherits reals_as_rational_cuts. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectMove {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.move priority moves) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨values,distinct,reads,rfl,rfl⟩ :=
    Move.sourceSuccess priority moves source sourcePost result execution notError
  have evens : (∀ n ∈ moves.map Prod.fst, n % 2=0) ∧
      (∀ n ∈ moves.map Prod.snd, n % 2=0) := by
    have raw : (∀ a b, (a,b) ∈ moves → a % 2=0) ∧
        (∀ a b, (a,b) ∈ moves → b % 2=0) := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar,List.all_eq_true] using conventions
    constructor
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.1 a b input
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.2 a b input
  have wf : sptWf source.locals=true := by
    unfold stateRel at related
    tauto
  obtain ⟨post,run,relation,_,_⟩ := Move.actualScheduledRun ac k f frame lens moves source target
    related distinct evens.1 evens.2 (by simp [reads]) (by simpa [maxVarHOL] using maxBound)
  rw [Move.scheduledSourceStateReconstruction moves source target k values distinct
    evens.1 evens.2 reads wf] at relation
  have program := congrArg Prod.fst compilation
  simp only [compNative] at program
  subst compiled
  refine ⟨0,post,none,?_,?_⟩
  · simpa only [Nat.add_zero] using run
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,↓reduceIte] using relation
end Flapjack.WordToStackProofs.CompCorrect.MoveFull
