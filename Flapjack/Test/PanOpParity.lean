import Flapjack.Semantics

/-!
# `panSem$pan_op_def` parity

The expected values are checked-in direct HOL-EVAL results from
`scripts/hol-probes/pan_op_probeScript.sml`, evaluating
`cakeml/pancake/semantics/panSemScript.sml:191-193`.  The fixture exercises the
successful two-word case and the original definition's rejection of the
wrong operand shapes.
-/

namespace Flapjack.Test.PanOpParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:191-193 (pan_op_def)"

def originalProbeCommand : String := "scripts/hol-probes/regenerate.sh"

def originalMulTwo : Option (BitVec 64) := some (BitVec.ofNat 64 15)
def originalMulOne : Option (BitVec 64) := none
def originalMulThree : Option (BitVec 64) := none

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:191-193 (pan_op_def)"
#guard originalProbeCommand == "scripts/hol-probes/regenerate.sh"

example : evalPanOp .mul [BitVec.ofNat 64 3, BitVec.ofNat 64 5] =
    originalMulTwo := by
  rfl

example : evalPanOp .mul [BitVec.ofNat 64 3] = originalMulOne := by
  rfl

example : evalPanOp .mul
    [BitVec.ofNat 64 3, BitVec.ofNat 64 5, BitVec.ofNat 64 7] =
    originalMulThree := by
  rfl

end Flapjack.Test.PanOpParity
