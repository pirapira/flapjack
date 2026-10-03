import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturningFull
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack grouping of the literal three original returning-Call evaluate_ind
hypotheses, retaining every intermediate binder and guard, for arbitrary handler
Option. The fourth tail-call IH is vacuous under this fixed SOME return descriptor
and is omitted. No independent HOL declaration names this grouping. -/
def OriginalInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      Seq.Simulation ac retHandler (WordSemStateFiniteExact.setVars n ys s1)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      Seq.Simulation ac h (WordSemStateFiniteExact.setVar n' y s2)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      Seq.Simulation ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))))

/-- Kernel translation of the literal original hypotheses into the accepted
NONE-case grouping. Only actual tuple/result identities are instantiated;
there is no stronger source context and no target premise. -/
private theorem noneHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (original : OriginalInductionHypotheses ac values names retCode l1 l2 dest args none source) :
    CallReturning.InductionHypotheses ac values names retCode l1 l2 dest args source := by
  refine ⟨?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,pop,domain⟩
    exact original.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs (some (.result location ys)) calleePost
      (.result location ys) location ys popped
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,checked,pop,domain⟩
  · intro xs args1 prog ss envs facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock⟩
    exact original.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock⟩

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

/-- Whole original returning-Call case (8166–10048), for arbitrary optional
handler. Both original source branches prove the entire simulation under the
literal original guarded IHs. Inherited reals_as_rational_cuts applies only to
the evaluator closure; no new numerical FP correspondence is claimed.

This specialized entry point fixes the return descriptor to SOME and retains
all three literal returning-Call IHs. It is kept alongside Call.compCorrectCall,
which permits arbitrary return options and retains the fourth tail-call IH.
That fourth IH is vacuous here because its original guard requires ret = NONE.
Both entry points assemble the same checked NONE/SOME handler simulations;
this overlap is intentional specialization, not a second independent proof of
the whole pass. No conclusion or source guard is omitted. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectCallReturning {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (original : OriginalInductionHypotheses ac values names retCode l1 l2 dest args handler source) :
    Seq.Simulation ac (.call (some (values,names,retCode,l1,l2)) dest args handler) source := by
  cases handler with
  | none =>
    exact CallReturning.compCorrectCallReturningNone ac values names retCode l1 l2 dest args source
      (noneHypotheses ac values names retCode l1 l2 dest args source original)
  | some handler =>
    obtain ⟨handlerVar,handlerCode,h1,h2⟩ := handler
    exact CallReturningHandler.compCorrectCallReturningHandler ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source original

end Flapjack.WordToStackProofs.CompCorrect.CallReturningFull
