import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Full intrinsic-domain decoder compositions needed by the original Const
constructor. These are Flapjack infrastructure, with no separately named HOL
composition declarations; source comparison and original boundary probes are
recorded with this section. Original Encode lines19135/19162/19189 and19252/19279 use Itype opcode0010011 with funct3 001/100/110, and Rtype opcode0110011 with funct3 100/110 and funct7=0. Decode lines15225/15289/15377/15610/15710 reconstruct rd11..7, rs19..15, imm31..20, shamt25..20 or rs2 24..20. SLLI high six bits are zero; every intrinsic shamt6 is retained. No target evaluation or input bounds are premises. -/

namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) : holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem reconstruct12 (w : BitVec 12) : holV2w 12 [w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8, w.getLsbD 7, w.getLsbD 6, w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem reconstruct6 (w : BitVec 6) : holV2w 6 [w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_ori (rd rs : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.ArithI (.ORI (rd, rs, imm))))) =
      .ArithI (.ORI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct12 imm⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_xori (rd rs : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.ArithI (.XORI (rd, rs, imm))))) =
      .ArithI (.XORI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct12 imm⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_slli (rd rs : BitVec 5) (imm : BitVec 6) :
    Step.DecodeAny (.Word (Encode (.Shift (.SLLI (rd, rs, imm))))) =
      .Shift (.SLLI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct6 imm⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_or (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.ArithR (.OR (rd, rs, rs2))))) =
      .ArithR (.OR (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_xor (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.ArithR (.XOR (rd, rs, rs2))))) =
      .ArithR (.XOR (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

end Flapjack.RiscV.L3
