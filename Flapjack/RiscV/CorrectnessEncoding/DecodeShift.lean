import Flapjack.RiscV.CorrectnessEncoding.DecodeConst

/-! Full intrinsic-domain native Shift decoding prerequisites for the original
encoder Shift case560-620, including both Ror instruction sequences. SLLI is
already proved in DecodeConst; this module supplies the five missing forms.
Register SLL/SRL/SRA use opcode0110011, funct3=001/101/101, funct7=0/0/32.
Immediate SRLI/SRAI use opcode0010011, funct3=101, funct6=0/16 and arbitrary
word6 amounts. All word5 registers and all intrinsic word6 amounts are retained.
These local Encode/DecodeAny compositions have no separately named HOL original
and remain untagged infrastructure; no target execution or extra bounds are assumed. -/
namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) : holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem reconstruct6 (w : BitVec 6) : holV2w 6 [w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

/-- Unrestricted literal native Shift Encode/DecodeAny composition. No
separately named HOL original; untagged infrastructure for the full encoder. -/
theorem decode_encode_sll (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.Shift (.SLL (rd, rs, rs2))))) =
      .Shift (.SLL (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted literal native Shift Encode/DecodeAny composition. No
separately named HOL original; untagged infrastructure for the full encoder. -/
theorem decode_encode_srl (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.Shift (.SRL (rd, rs, rs2))))) =
      .Shift (.SRL (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted literal native Shift Encode/DecodeAny composition. No
separately named HOL original; untagged infrastructure for the full encoder. -/
theorem decode_encode_sra (rd rs : BitVec 5) (rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.Shift (.SRA (rd, rs, rs2))))) =
      .Shift (.SRA (rd, rs, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct5 rs2⟩

/-- Unrestricted literal native Shift Encode/DecodeAny composition. No
separately named HOL original; untagged infrastructure for the full encoder. -/
theorem decode_encode_srli (rd rs : BitVec 5) (imm : BitVec 6) :
    Step.DecodeAny (.Word (Encode (.Shift (.SRLI (rd, rs, imm))))) =
      .Shift (.SRLI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct6 imm⟩

/-- Unrestricted literal native Shift Encode/DecodeAny composition. No
separately named HOL original; untagged infrastructure for the full encoder. -/
theorem decode_encode_srai (rd rs : BitVec 5) (imm : BitVec 6) :
    Step.DecodeAny (.Word (Encode (.Shift (.SRAI (rd, rs, imm))))) =
      .Shift (.SRAI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct6 imm⟩

end Flapjack.RiscV.L3
