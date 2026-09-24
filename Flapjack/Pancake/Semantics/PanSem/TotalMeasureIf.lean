import Flapjack.Pancake.Semantics.PanSem.Total
import Flapjack.Pancake.Semantics.PanSem.TotalSteps

/-!
# Measure-driven total PanSem control fragment

This module is an incremental evaluator step over the explicit
`PanSemExprIfFragmentRiscV64` domain. Its recursive calls are justified by the
same `(clock, panSemProgFuel)` measure intended for the full `evaluate_def`
port. It evaluates conditions from the complete `PanSemState`, applies HOL
`fix_clock` between sequence commands, and uses the HOL-shaped total clause
helpers for Assign/Return/Raise. Other `Prog` constructors remain outside the
domain, so this is untagged support and does not claim the whole
`evaluate_def` clause.
-/

namespace Flapjack

variable {σ : Type v}

/-- Total recursive evaluation of the RV64 clock-leaf/Seq/If/Assign/Return/
    Raise fragment using the source evaluator's lexicographic measure. The
    fragment embeds into production `Prog`; the measure is therefore the same
    one used to justify recursive calls in the planned whole-program evaluator.
    Assign/Return/Raise use the shared expression and clause steps from
    `TotalSteps`; all such cases preserve the complete state on Error. -/
def panSemEvaluateExprIfFragmentRiscV64ByMeasure [NeZero 64]
    [BEq (RiscV.Word 64)] [DecidableEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    : PanSemExprIfFragmentRiscV64 →
    PanSemState (RiscV.Word 64) (FfiState σ) →
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ)
  | .leaf leaf, state => panSemEvaluateClockLeaf leaf state
  | .seq first second, state =>
      let (result, firstState) :=
        panSemEvaluateExprIfFragmentRiscV64ByMeasure first state
      let fixedState := panSemFixClock state.clock firstState
      match result with
      | none => panSemEvaluateExprIfFragmentRiscV64ByMeasure second fixedState
      | some result => (some result, fixedState)
  | .ite condition thenBranch elseBranch, state =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then
            panSemEvaluateExprIfFragmentRiscV64ByMeasure elseBranch state
          else
            panSemEvaluateExprIfFragmentRiscV64ByMeasure thenBranch state
      | _ => (some .error, state)
  | .assign kind name expression, state =>
      panSemTotalAssignClause state kind name expression
  | .returnValue expression, state =>
      panSemTotalReturnClause state expression
  | .raiseException exception expression, state =>
      panSemTotalRaiseClause state exception expression
termination_by program state => panSemEvalMeasure state program.toProg
decreasing_by
  · change panSemEvalMeasureRel (state, first.toProg)
      (state, Prog.seq first.toProg second.toProg)
    exact panSemEvalMeasureRel_seq_branch state state first.toProg second.toProg
      first.toProg (Nat.le_refl _) (Or.inl rfl)
  · change panSemEvalMeasureRel (fixedState, second.toProg)
      (state, Prog.seq first.toProg second.toProg)
    exact panSemEvalMeasureRel_seq_branch fixedState state first.toProg second.toProg
      second.toProg (panSemFixClock_clock_le state.clock firstState) (Or.inr rfl)
  · change panSemEvalMeasureRel (state, elseBranch.toProg)
      (state, Prog.ite condition thenBranch.toProg elseBranch.toProg)
    exact panSemEvalMeasureRel_ite_branch state condition thenBranch.toProg
      elseBranch.toProg elseBranch.toProg (Or.inr rfl)
  · change panSemEvalMeasureRel (state, thenBranch.toProg)
      (state, Prog.ite condition thenBranch.toProg elseBranch.toProg)
    exact panSemEvalMeasureRel_ite_branch state condition thenBranch.toProg
      elseBranch.toProg thenBranch.toProg (Or.inl rfl)

end Flapjack
