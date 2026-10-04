import Flapjack.Pancake.Proofs.PanToTarget

/-! Kernel replay of the six fresh boundary rows in the explicitly identified
literal HOL source replay pan_to_target_option_lt_source_replay_probe.out.
The captured definition has all three original clauses; no unknown bound is invented. -/
namespace Flapjack.Test.PanToTargetOptionLtParity
open Flapjack.Pancake.Proofs.PanToTarget

def sourceRows : Bool :=
  optionLt none none && optionLt (some 4) none &&
  !(optionLt none (some 4)) && optionLt (some 3) (some 4) &&
  !(optionLt (some 4) (some 4)) && !(optionLt (some 5) (some 4))

#guard sourceRows

theorem sourceRows_proof : sourceRows = true := by
  simp [sourceRows, optionLt]

end Flapjack.Test.PanToTargetOptionLtParity
