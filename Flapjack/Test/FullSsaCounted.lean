import Flapjack.RiscV.CorrectnessFullSsaCounted
import Flapjack.Test.FullSsaPipeline

namespace Flapjack

open RiscV

/-! The concrete full-SSA image also satisfies the machine count contract.
    This checks the count against the generated artifact without adding a
    second expensive native execution. -/

theorem fullSsaMain_counted_image_length :
    (fullSsaMainImage.map fun image =>
      (RiscV.executeInstructionsCounted (RiscV.zeroState 64) image).2) =
      fullSsaMainImage.map List.length := by
  cases himage : fullSsaMainImage with
  | none => simp
  | some image =>
      simp [RiscV.executeInstructionsCounted_spec]

end Flapjack
