import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
Production-carrier analogue of HOL `compile_prog_distinct_params`; the
faithful exact-carrier theorem depends on the exact `compile_prog` port.
-/

namespace Flapjack

/-- FLAPJACK-SPECIFIC analogue of HOL `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4691`): every function compiled from a
    source declaration has distinct flattened parameter slots. HOL quantifies
    over its positive-width word-indexed `prog` and concludes about exact
    `compile_prog` triples whose names are `mlstring` and bodies are
    `CrepProgHOL width`. This theorem instead quantifies over production
    `Decl (BitVec width)` (String names, production Shape/Prog) and concludes
    about `compileProgTopHOL` (production String/CrepProg); it also admits
    `BitVec 0`. No existing qualifier authorizes those carrier and width
    differences. Keep this useful analogue untagged; port the result over
    `DeclHOL` and the exact `compile_prog` output with the exact compiler
    work tracked by `flapjack-4ac.2.20`. -/
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
