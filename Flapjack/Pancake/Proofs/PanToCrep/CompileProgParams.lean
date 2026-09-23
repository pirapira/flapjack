import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
HOL `compile_prog_distinct_params` at the exact triple-list boundary.
-/

namespace Flapjack

/-- HOL `compile_prog_distinct_params`: every function compiled from a source
    declaration has distinct flattened parameter slots. The original theorem
    has no premise. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_prog_distinct_params"]
theorem compileProgTopHOL_params_nodup
    (declarations : List (Decl (BitVec width))) :
    ∀ function ∈ compileProgTopHOL declarations,
      function.2.1.Nodup := by
  intro function hfunction
  simp [compileProgTopHOL, compileInlTopHOL,
    compileToCrepHOL, panToCrepVars] at hfunction
  rcases hfunction with ⟨name, params, body, _hsource, heq⟩
  cases heq
  exact List.nodup_range

end Flapjack
