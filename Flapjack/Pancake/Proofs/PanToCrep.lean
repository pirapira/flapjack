import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanToCrepMaxList

/-!
Faithful HOL-facing relations and contexts for the Pancake `pan_to_crep`
correctness proof.  The definitions here use the extensional finite-map model
from `Flapjack.FiniteMap`, rather than the list-backed executable compiler
context.
-/

namespace Flapjack

/-! The HOL proof context record used by `ctxt_fc_def`. -/
structure PanToCrepProofContext (α : Type) where
  vars : FiniteMap String (Shape × List Nat)
  funcs : FiniteMap String (List (String × Shape) × Shape)
  eids : FiniteMap String α
  vmax : Nat

/-! HOL `excp_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:16`).
    This states equality of exception-code map domains and injectivity of the
    compiler's code map on its defined entries; the source exception map's
    values need not equal the compiler's values. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "excp_rel_def"]
def excpRel
    (compilerCodes : FiniteMap String α)
    (sourceShapes : FiniteMap String β) : Prop :=
  FDOM sourceShapes = FDOM compilerCodes ∧
    ∀ exception exception' code code',
      FLOOKUP compilerCodes exception = some code →
      FLOOKUP compilerCodes exception' = some code' →
      code = code' → exception = exception'

/-! HOL `ctxt_fc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25`).
    `FUPDATE_LIST` and `withShape` preserve the source definition's ZIP
    truncation and TAKE/DROP slicing, and `maxList` is Cake's `MAX_LIST`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_def"]
def ctxtFc
    (compilerFunctions : FiniteMap String (List (String × Shape) × Shape))
    (exceptionCodes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) : PanToCrepProofContext α :=
  { vars := FUPDATE_LIST FEMPTY
      (variables.zip (shapes.zip (withShape shapes names)))
    funcs := compilerFunctions
    eids := exceptionCodes
    vmax := maxList names }

end Flapjack
