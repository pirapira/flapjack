import Flapjack.Pancake.Proofs.PanToTarget.CompileProgMax
import Flapjack.HolRef

/-!
# CakeML Pancake `pan_to_targetProof`

Counterpart of `cakeml/pancake/proofs/pan_to_targetProofScript.sml`. This
module holds standalone definition ports from that proof script. The
`compile_prog_max` wrapper and the full source-to-target theorem remain open.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

/-- Exact HOL `option_lt`
    (`cakeml/pancake/proofs/pan_to_targetProofScript.sml:1157-1159`):
    `option_lt n0 NONE ⇔ T`, `option_lt NONE (SOME n1) ⇔ F`, and
    `option_lt (SOME n1) (SOME n2) ⇔ n1 < n2`. HOL `bool` is rendered by Lean
    `Bool`; the carrier is otherwise identity.

    The probe replays the literal three-clause original definition in a separate
    HOL theory because the original proof theory is not compiled in the pinned
    oracle toolchain. Its typed equation and boundary observations are local
    source replays, not captures of an exported original theorem. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_def"]
def optionLt : Option Nat → Option Nat → Bool
  | _, none => true
  | none, some _ => false
  | some m, some n => m < n

end Flapjack.Pancake.Proofs.PanToTarget
