import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Symbolic decoding prerequisites of original Const/Loc encoder cases.
Utype concatenates the twenty immediate bits, five destination bits and
seven opcode bits. The literal decoder reconstructs imm from31..12 and
rd from11..7; LUI has opcode0110111 and AUIPC0010111.
These compositions have no separately named HOL original and are untagged
Flapjack infrastructure. No register or immediate value is restricted. -/
namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) :
    holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem reconstruct20 (w : BitVec 20) :
    holV2w 20 [w.getLsbD 19, w.getLsbD 18, w.getLsbD 17, w.getLsbD 16, w.getLsbD 15, w.getLsbD 14, w.getLsbD 13, w.getLsbD 12, w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8, w.getLsbD 7, w.getLsbD 6, w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

/-- Full-field LUI composition for native encoder correctness. There is no
separate named original theorem for this composition; the original Utype,
Encode and Decode clauses are retained without extra input premises. -/
theorem decode_encode_lui (rd : BitVec 5) (imm : BitVec 20) :
    Step.DecodeAny (.Word (Encode (.ArithI (.LUI (rd, imm))))) =
      .ArithI (.LUI (rd, imm)) := by
  simp only [Step.DecodeAny, Encode, Utype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct20 imm⟩

/-- Full-field AUIPC composition for native encoder correctness. There is no
separate named original theorem for this composition; the original Utype,
Encode and Decode clauses are retained without extra input premises. -/
theorem decode_encode_auipc (rd : BitVec 5) (imm : BitVec 20) :
    Step.DecodeAny (.Word (Encode (.ArithI (.AUIPC (rd, imm))))) =
      .ArithI (.AUIPC (rd, imm)) := by
  simp only [Step.DecodeAny, Encode, Utype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct20 imm⟩

end Flapjack.RiscV.L3
