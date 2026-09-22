import Flapjack.HolRef
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.ShapeInfrastructure

namespace Flapjack

/-! Exact-shaped port of Cake's \`compile_top_only_functions_or_exns\`
    (\`cakeml/pancake/proofs/pan_globalsProofScript.sml:2611\`). The public
    \`globalCompileTopForStart\` is total, so the missing-start branch is the
    empty list and satisfies the result predicate vacuously. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"
  "compile_top_only_functions_or_exns"]
theorem globalCompileTopForStart_all_function_or_exception [BEq String]
    [Add α] [Mul α] (bytesInWord : α) (fromNat : Nat → α)
    (declarations : List (Decl α)) (start : FunName) :
    (globalCompileTopForStart bytesInWord fromNat declarations start).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  unfold globalCompileTopForStart
  cases hfind : globalFindFunction start declarations with
  | none =>
      simp [globalCompileTopForStartSome, hfind]
  | some entry =>
      simp only [globalCompileTopForStartSome, hfind, Option.getD_some]
      exact globalCompileDecs_result_all_function_or_exception _ _ _
        (by simp [globalDeclIsFunction])

end Flapjack
