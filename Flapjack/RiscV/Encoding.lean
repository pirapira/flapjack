import Flapjack.RiscV.Model

/-!
# RISC-V instruction encoding

This is the concrete artifact boundary corresponding to CakeML's
`riscv_encode`/`riscv_enc`.  The typed instruction model is encoded as one
32-bit RV instruction and then emitted in little-endian byte order, matching
the `word8 list` produced by the HOL target encoder.
-/

namespace Flapjack.RiscV

def encodeWord32 (value : Nat) : BitVec 32 := BitVec.ofNat 32 value

def lowBits (value : Word width) (bits : Nat) : Nat :=
  value.toNat % 2 ^ bits

def registerBits (register : Fin 32) : Nat := register.val

def encodeR (opcode funct3 funct7 : Nat)
    (destination sourceLeft sourceRight : Fin 32) : BitVec 32 :=
  encodeWord32 (opcode +
    registerBits destination * 2 ^ 7 +
    funct3 * 2 ^ 12 +
    registerBits sourceLeft * 2 ^ 15 +
    registerBits sourceRight * 2 ^ 20 +
    funct7 * 2 ^ 25)

def encodeIValue (opcode funct3 : Nat) (destination source : Fin 32)
    (immediate : Nat) : BitVec 32 :=
  encodeWord32 (opcode +
    registerBits destination * 2 ^ 7 +
    funct3 * 2 ^ 12 +
    registerBits source * 2 ^ 15 +
    (immediate % 2 ^ 12) * 2 ^ 20)

def encodeI (opcode funct3 : Nat) (destination source : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  encodeIValue opcode funct3 destination source (lowBits immediate 12)

def encodeS (funct3 : Nat) (source address : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  let value := lowBits immediate 12
  encodeWord32 (0x23 +
    (value / 2 ^ 5 % 2 ^ 7) * 2 ^ 25 +
    registerBits source * 2 ^ 20 +
    registerBits address * 2 ^ 15 +
    funct3 * 2 ^ 12 +
    (value % 2 ^ 5) * 2 ^ 7)

def encodeB (funct3 : Nat) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) : BitVec 32 :=
  let value := lowBits offset 13
  encodeWord32 (0x63 +
    (value / 2 ^ 12 % 2) * 2 ^ 31 +
    (value / 2 ^ 5 % 2 ^ 6) * 2 ^ 25 +
    registerBits sourceRight * 2 ^ 20 +
    registerBits sourceLeft * 2 ^ 15 +
    funct3 * 2 ^ 12 +
    (value / 2 % 2 ^ 4) * 2 ^ 8 +
    (value / 2 ^ 11 % 2) * 2 ^ 7)

def encodeU (opcode : Nat) (destination : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  encodeWord32 (opcode + registerBits destination * 2 ^ 7 +
    lowBits immediate 20 * 2 ^ 12)

def encodeJ (destination : Fin 32) (offset : Word width) : BitVec 32 :=
  let value := lowBits offset 21
  encodeWord32 (0x6f + registerBits destination * 2 ^ 7 +
    (value / 2 ^ 12 % 2 ^ 8) * 2 ^ 12 +
    (value / 2 ^ 11 % 2) * 2 ^ 20 +
    (value / 2 ^ 1 % 2 ^ 10) * 2 ^ 21 +
    (value / 2 ^ 20 % 2) * 2 ^ 31)

def encodeInstruction [NeZero width] : Instruction width → BitVec 32
  | .add destination sourceLeft sourceRight =>
      encodeR 0x33 0 0 destination sourceLeft sourceRight
  | .sub destination sourceLeft sourceRight =>
      encodeR 0x33 0 0x20 destination sourceLeft sourceRight
  | .addW destination sourceLeft sourceRight =>
      encodeR 0x3b 0 0 destination sourceLeft sourceRight
  | .subW destination sourceLeft sourceRight =>
      encodeR 0x3b 0 0x20 destination sourceLeft sourceRight
  | .and destination sourceLeft sourceRight =>
      encodeR 0x33 7 0 destination sourceLeft sourceRight
  | .or destination sourceLeft sourceRight =>
      encodeR 0x33 6 0 destination sourceLeft sourceRight
  | .xor destination sourceLeft sourceRight =>
      encodeR 0x33 4 0 destination sourceLeft sourceRight
  | .addi destination source immediate => encodeI 0x13 0 destination source immediate
  | .addiW destination source immediate => encodeI 0x1b 0 destination source immediate
  | .andi destination source immediate => encodeI 0x13 7 destination source immediate
  | .ori destination source immediate => encodeI 0x13 6 destination source immediate
  | .xori destination source immediate => encodeI 0x13 4 destination source immediate
  | .mul destination sourceLeft sourceRight =>
      encodeR 0x33 0 1 destination sourceLeft sourceRight
  | .mulW destination sourceLeft sourceRight =>
      encodeR 0x3b 0 1 destination sourceLeft sourceRight
  | .mulHU destination sourceLeft sourceRight =>
      encodeR 0x33 3 1 destination sourceLeft sourceRight
  | .sll destination sourceLeft sourceRight =>
      encodeR 0x33 1 0 destination sourceLeft sourceRight
  | .srl destination sourceLeft sourceRight =>
      encodeR 0x33 5 0 destination sourceLeft sourceRight
  | .sra destination sourceLeft sourceRight =>
      encodeR 0x33 5 0x20 destination sourceLeft sourceRight
  | .sllW destination sourceLeft sourceRight =>
      encodeR 0x3b 1 0 destination sourceLeft sourceRight
  | .srlW destination sourceLeft sourceRight =>
      encodeR 0x3b 5 0 destination sourceLeft sourceRight
  | .sraW destination sourceLeft sourceRight =>
      encodeR 0x3b 5 0x20 destination sourceLeft sourceRight
  | .slli destination source amount =>
      encodeIValue 0x13 1 destination source (shiftAmount amount)
  | .srli destination source amount =>
      encodeIValue 0x13 5 destination source (shiftAmount amount)
  | .srai destination source amount =>
      encodeIValue 0x13 5 destination source (0x20 * 2 ^ 5 + shiftAmount amount)
  | .slliW destination source amount =>
      encodeIValue 0x1b 1 destination source (amount.toNat % 32)
  | .srliW destination source amount =>
      encodeIValue 0x1b 5 destination source (amount.toNat % 32)
  | .sraiW destination source amount =>
      encodeIValue 0x1b 5 destination source (0x20 * 2 ^ 5 + amount.toNat % 32)
  | .slt destination sourceLeft sourceRight =>
      encodeR 0x33 2 0 destination sourceLeft sourceRight
  | .slti destination source immediate => encodeI 0x13 2 destination source immediate
  | .sltu destination sourceLeft sourceRight =>
      encodeR 0x33 3 0 destination sourceLeft sourceRight
  | .sltiu destination source immediate => encodeI 0x13 3 destination source immediate
  | .lui destination immediate => encodeU 0x37 destination immediate
  | .auipc destination immediate => encodeU 0x17 destination immediate
  | .divU destination sourceLeft sourceRight =>
      encodeR 0x33 5 1 destination sourceLeft sourceRight
  | .remU destination sourceLeft sourceRight =>
      encodeR 0x33 7 1 destination sourceLeft sourceRight
  | .branchEq sourceLeft sourceRight offset => encodeB 0 sourceLeft sourceRight offset
  | .branchNe sourceLeft sourceRight offset => encodeB 1 sourceLeft sourceRight offset
  | .branchLt sourceLeft sourceRight offset => encodeB 4 sourceLeft sourceRight offset
  | .branchGe sourceLeft sourceRight offset => encodeB 5 sourceLeft sourceRight offset
  | .branchLtU sourceLeft sourceRight offset => encodeB 6 sourceLeft sourceRight offset
  | .branchGeU sourceLeft sourceRight offset => encodeB 7 sourceLeft sourceRight offset
  | .jal destination offset => encodeJ destination offset
  | .jalr destination source offset => encodeI 0x67 0 destination source offset
  | .ecall => encodeWord32 0x73
  | .loadByte destination address => encodeIValue 0x03 4 destination address 0
  | .loadByteSigned destination address => encodeIValue 0x03 0 destination address 0
  | .storeByte source address =>
      encodeS (width := width) 0 source address (BitVec.ofNat width 0)
  | .loadHalf destination address => encodeIValue 0x03 5 destination address 0
  | .loadHalfSigned destination address => encodeIValue 0x03 1 destination address 0
  | .storeHalf source address =>
      encodeS (width := width) 1 source address (BitVec.ofNat width 0)
  | .load32 destination address => encodeIValue 0x03 6 destination address 0
  | .store32 source address =>
      encodeS (width := width) 2 source address (BitVec.ofNat width 0)
  | .loadWord destination address => encodeIValue 0x03 3 destination address 0
  | .storeWord source address =>
      encodeS (width := width) 3 source address (BitVec.ofNat width 0)

def encodeWordBytes (value : BitVec 32) : List (BitVec 8) :=
  [ BitVec.ofNat 8 (value.toNat % 256)
  , BitVec.ofNat 8 (value.toNat / 256 % 256)
  , BitVec.ofNat 8 (value.toNat / (256 ^ 2) % 256)
  , BitVec.ofNat 8 (value.toNat / (256 ^ 3) % 256) ]

def encodeInstructionBytes [NeZero width] (instruction : Instruction width) :
    List (BitVec 8) :=
  encodeWordBytes (encodeInstruction instruction)

def encodeInstructions [NeZero width] : List (Instruction width) → List (BitVec 8)
  | [] => []
  | instruction :: instructions =>
      encodeInstructionBytes instruction ++ encodeInstructions instructions

structure EncodedRiscVSection (width : Nat) where
  label : Nat
  address : Word width
  bytes : List (BitVec 8)
  deriving Repr

def encodeLinkedSections [NeZero width] :
    List (Nat × Word width × List (Instruction width)) →
      List (EncodedRiscVSection width)
  | [] => []
  | (label, address, instructions) :: sections =>
      { label, address, bytes := encodeInstructions instructions } ::
        encodeLinkedSections sections

@[simp] theorem encodeInstructionBytes_length [NeZero width]
    (instruction : Instruction width) :
    (encodeInstructionBytes instruction).length = 4 := by
  simp [encodeInstructionBytes, encodeWordBytes]

theorem encodeInstructions_length [NeZero width]
    (instructions : List (Instruction width)) :
    (encodeInstructions instructions).length = 4 * instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions induction =>
      simp [encodeInstructions, encodeInstructionBytes_length, induction]
      omega

end Flapjack.RiscV
