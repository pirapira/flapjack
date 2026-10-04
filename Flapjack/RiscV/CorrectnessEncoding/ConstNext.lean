import Flapjack.RiscV.CorrectnessEncoding.InstructionStep
import Flapjack.RiscV.CorrectnessEncoding.DecodeConst
import Flapjack.RiscV.L3.Defs.Run

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Exact four native memory bytes of an emitted instruction; untagged
infrastructure, not a separately named original HOL declaration. -/
def encodedInstructionBytes (ms : riscv_state) (i : instruction) : Prop :=
  let w := Encode i
  ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w ∧
  ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w ∧
  ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w ∧
  ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w

/-- Native LUI Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_lui (ms : riscv_state) (rd : BitVec 5) (imm : BitVec 20)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithI (.LUI (rd,imm)))) :
    NextRISCV ms = some (writePost ms rd (((imm ++ 0#12).signExtend 64))) := by
  have lowbits : (Encode (.ArithI (.LUI (rd,imm)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.LUI (rd,imm)))).getLsbD 1 = true := by
    simp only [Encode, Utype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithI (.LUI (rd,imm))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (((imm ++ 0#12).signExtend 64),rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'LUI»]
  exact write_next ms (.ArithI (.LUI (rd,imm))) (Encode (.ArithI (.LUI (rd,imm)))) rd (((imm ++ 0#12).signExtend 64))
    rn ok (decode_encode_lui _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native ADDI Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_addi (ms : riscv_state) (rd rs : BitVec 5) (imm : BitVec 12)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithI (.ADDI (rd,rs,imm)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms + imm.signExtend 64)) := by
  have lowbits : (Encode (.ArithI (.ADDI (rd,rs,imm)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.ADDI (rd,rs,imm)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithI (.ADDI (rd,rs,imm))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms + imm.signExtend 64,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'ADDI», GPR, gpr]
  exact write_next ms (.ArithI (.ADDI (rd,rs,imm))) (Encode (.ArithI (.ADDI (rd,rs,imm)))) rd (GPR rs ms + imm.signExtend 64)
    rn ok (decode_encode_addi _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native ORI Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_ori (ms : riscv_state) (rd rs : BitVec 5) (imm : BitVec 12)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithI (.ORI (rd,rs,imm)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms ||| imm.signExtend 64)) := by
  have lowbits : (Encode (.ArithI (.ORI (rd,rs,imm)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.ORI (rd,rs,imm)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithI (.ORI (rd,rs,imm))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms ||| imm.signExtend 64,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'ORI», GPR, gpr]
  exact write_next ms (.ArithI (.ORI (rd,rs,imm))) (Encode (.ArithI (.ORI (rd,rs,imm)))) rd (GPR rs ms ||| imm.signExtend 64)
    rn ok (decode_encode_ori _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native XORI Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_xori (ms : riscv_state) (rd rs : BitVec 5) (imm : BitVec 12)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithI (.XORI (rd,rs,imm)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms ^^^ imm.signExtend 64)) := by
  have lowbits : (Encode (.ArithI (.XORI (rd,rs,imm)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.XORI (rd,rs,imm)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithI (.XORI (rd,rs,imm))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms ^^^ imm.signExtend 64,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'XORI», GPR, gpr]
  exact write_next ms (.ArithI (.XORI (rd,rs,imm))) (Encode (.ArithI (.XORI (rd,rs,imm)))) rd (GPR rs ms ^^^ imm.signExtend 64)
    rn ok (decode_encode_xori _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native SLLI Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_slli (ms : riscv_state) (rd rs : BitVec 5) (shamt : BitVec 6)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.Shift (.SLLI (rd,rs,shamt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms <<< shamt.toNat)) := by
  have lowbits : (Encode (.Shift (.SLLI (rd,rs,shamt)))).getLsbD 0 = true ∧
      (Encode (.Shift (.SLLI (rd,rs,shamt)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.Shift (.SLLI (rd,rs,shamt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms <<< shamt.toNat,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simp [Run, «dfn'SLLI», in32BitMode, curArch, architecture, MCSR, arch, GPR, gpr]
  exact write_next ms (.Shift (.SLLI (rd,rs,shamt))) (Encode (.Shift (.SLLI (rd,rs,shamt)))) rd (GPR rs ms <<< shamt.toNat)
    rn ok (decode_encode_slli _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native OR Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_or (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithR (.OR (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms ||| GPR rt ms)) := by
  have lowbits : (Encode (.ArithR (.OR (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.ArithR (.OR (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithR (.OR (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms ||| GPR rt ms,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'OR», GPR, gpr]
  exact write_next ms (.ArithR (.OR (rd,rs,rt))) (Encode (.ArithR (.OR (rd,rs,rt)))) rd (GPR rs ms ||| GPR rt ms)
    rn ok (decode_encode_or _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Native XOR Next from actual encoded bytes and original
riscv_ok; literal Run/Decode are proved internally, not target assumptions.
No separately named HOL composition exists, so this helper is untagged. -/
theorem next_encoded_xor (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithR (.XOR (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms ^^^ GPR rt ms)) := by
  have lowbits : (Encode (.ArithR (.XOR (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.ArithR (.XOR (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithR (.XOR (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms ^^^ GPR rt ms,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'XOR», GPR, gpr]
  exact write_next ms (.ArithR (.XOR (rd,rs,rt))) (Encode (.ArithR (.XOR (rd,rs,rt)))) rd (GPR rs ms ^^^ GPR rt ms)
    rn ok (decode_encode_xor _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

end Flapjack.RiscV.TargetProof
