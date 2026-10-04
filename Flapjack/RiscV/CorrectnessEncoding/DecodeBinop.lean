import Mathlib.Tactic.IntervalCases
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Universal native Binop Encode/Decode compositions. All intrinsic word5
register and word12 immediate operands are retained. These local compositions
have no separately named HOL declaration and remain untagged infrastructure.
Original Encode19195-19220/19285-19293 and Decode15399/15437/15473/15742
retain rd11..7, rs1 19..15, rs2 24..20 or imm31..20. ANDI uses
opcode0010011/funct3=111; ADD/SUB/AND use opcode0110011, funct3=000/000/111
and funct7=0/32/0 respectively. No successful target run or register bound
is added; the intrinsic operand carrier supplies the original fixed widths. -/
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

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_andi (rd rs : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.ArithI (.ANDI (rd, rs, imm))))) =
      .ArithI (.ANDI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct12 imm⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_add (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.ArithR (.ADD (rd, rs, rs2))))) =
      .ArithR (.ADD (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_sub (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.ArithR (.SUB (rd, rs, rs2))))) =
      .ArithR (.SUB (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted composition of original native Encode and Decode clauses;
no distinct named HOL original, so this infrastructure remains untagged. -/
theorem decode_encode_and (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.ArithR (.AND (rd, rs, rs2))))) =
      .ArithR (.AND (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

end Flapjack.RiscV.L3
