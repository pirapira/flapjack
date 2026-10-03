import Mathlib.Tactic.IntervalCases
import Flapjack.RiscV.L3.Support

namespace Flapjack.RiscV.TargetProof
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Value reconstruction for the two literal wide Const branches. This is
untagged infrastructure, with no separately named HOL identity. Every word64
is retained; it supplies no target-run or range premise. -/
theorem const_wide_value_reconstruction (c : BitVec 64) :
    (if c.getLsbD 31 then
      ((~~~(c.extractLsb' 32 32)).signExtend 64 <<< 32) ^^^
        ((c.extractLsb' 0 32).signExtend 64)
     else
      ((c.extractLsb' 32 32).signExtend 64 <<< 32) |||
        ((c.extractLsb' 0 32).signExtend 64)) = c := by
  cases bit : c.getLsbD 31
  all_goals
    have hbit := bit
    change c[31] = _ at hbit
    simp only [Bool.false_eq_true, ite_false, ite_true]
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
      BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_not,
      BitVec.getLsbD_extractLsb']
    interval_cases i <;> simp [hbit]

end Flapjack.RiscV.TargetProof
