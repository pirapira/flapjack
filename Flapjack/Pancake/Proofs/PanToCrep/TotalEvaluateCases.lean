import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanSem.TotalMeasureIf
import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-!
# Total evaluator cases for Pan-to-Crep correctness

The declarations here assemble selected constructor cases from the total,
HOL-result-shaped source and target evaluator clauses. They are induction-case
support for `pc_compile_correct`; they do not claim the complete evaluator
induction or receive a standalone `@[hol]` reference.
-/

namespace Flapjack

/-! The `Skip` constructor case uses the total result×state clauses on both
  sides. The source evaluator uses the production `PanSemState`, and the target
  evaluator uses the code-bearing runtime state converted by `toHolState`. The
  compiled target syntax is exactly `Skip`. The returned runtime post-state is
  the original target state, so all four state/code/exception/local relations
  are established at the post-state boundary without a target-run premise. -/
theorem panToCrepTotalSkipStateCase
    {σ : Type _}
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code)
      targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateExprIfFragmentRiscV64ByMeasure (.leaf .skip) sourceState =
        (none, sourceState) ∧
    compileCodeRelProg context (.skip : Prog (RiscV.Word 64)) =
        (CrepProg.skip : CrepProg (BitVec 64)) ∧
    ∃ targetPost : CrepRuntimeState (RiscV.Word 64) σ,
      evalCrepClockLeaf .skip targetState.toHolState =
          (none, targetPost.toHolState) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧
      localsRel context sourceState.locals targetPost.locals := by
  refine ⟨by simp [panSemEvaluateExprIfFragmentRiscV64ByMeasure], rfl, ?_⟩
  refine ⟨targetState, by simp, hstate, ?_, hexcp, hlocals⟩
  exact hcode

end Flapjack
