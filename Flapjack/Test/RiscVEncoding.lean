import Flapjack.RiscV.Encoding

namespace Flapjack.RiscV

def byte (value : Nat) : BitVec 8 := BitVec.ofNat 8 value

example :
    encodeInstructionBytes (.add (1 : Fin 32) 2 3 : Instruction 64) =
      [byte 0xb3, byte 0x00, byte 0x31, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.addi (1 : Fin 32) 0 (BitVec.ofNat 64 7)) =
      [byte 0x93, byte 0x00, byte 0x70, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.loadWord (1 : Fin 32) 2 : Instruction 64) =
      [byte 0x83, byte 0x30, byte 0x01, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.storeWord (1 : Fin 32) 2 : Instruction 64) =
      [byte 0x23, byte 0x30, byte 0x11, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.branchEq (1 : Fin 32) 2 (BitVec.ofNat 64 8)) =
      [byte 0x63, byte 0x84, byte 0x20, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.jal 0 (BitVec.ofNat 64 8)) =
      [byte 0x6f, byte 0x00, byte 0x80, byte 0x00] := by
  decide

example :
    encodeInstructionBytes (.ecall : Instruction 64) =
      [byte 0x73, byte 0x00, byte 0x00, byte 0x00] := by
  decide

example :
    encodeInstructions
      [.addi (1 : Fin 32) 0 (BitVec.ofNat 64 7), .ecall] =
      [byte 0x93, byte 0x00, byte 0x70, byte 0x00,
       byte 0x73, byte 0x00, byte 0x00, byte 0x00] := by
  decide

example :
    (encodeInstructions
      ([.add (1 : Fin 32) 2 3, .ecall] : List (Instruction 64))).length = 8 := by
  simp [encodeInstructions_length]

end Flapjack.RiscV
