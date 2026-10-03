import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveSingle
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.WordToStackProofs.MoveAux
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Flapjack all-outcome evaluator calculation: trailing Skip preserves the
actual result, because the evaluated postclock is already bounded by its input.
No target evaluation outcome or clock relation is assumed. -/
private theorem trailingSkip {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq program .skip,target) =
      StackSemEvaluate.evaluate (program,target) := by
  rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate]
  rcases run : StackSemEvaluate.evaluate (program,target) with ⟨result,post⟩
  cases result
  · exact StackSemEvaluate.evaluate_skip post
  · rfl

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original empty/cons move-list evaluator unfolding2856–2867.
Arbitrary formatted moves, target states and frame tuples, including failures
and every result, are retained. Inherited reals_as_rational_cuts applies only
to the evaluator closure; no new FP correspondence is claimed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveAux_thm"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs,StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wMoveAuxThm {width : Nat} [NeZero width] {C F : Type}
    (move : Sum Nat Nat × Sum Nat Nat) (moves : List (Sum Nat Nat × Sum Nat Nat))
    (frame : Nat × Nat × Nat) (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (wMoveAuxNative [] frame,target) = (none,target) ∧
    StackSemEvaluate.evaluate (wMoveAuxNative (move::moves) frame,target) =
      StackSemEvaluate.evaluate (.seq (wMoveSingleNative move frame) (wMoveAuxNative moves frame),target) := by
  refine ⟨StackSemEvaluate.evaluate_skip target,?_⟩
  cases moves with
  | nil => exact (trailingSkip (wMoveSingleNative move frame) target).symm
  | cons next tail => rfl

end Flapjack.WordToStackProofs.MoveAux
