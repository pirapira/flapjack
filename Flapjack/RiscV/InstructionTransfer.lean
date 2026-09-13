import Flapjack.RiscV.RegisterTransfer

/-!
# RISC-V instruction register transfer

The RISC-V model uses hardware register indices.  CakeML's StackLang-facing
pipeline uses the internal indices whose hardware images are given by
`riscvForward`.  This definition maps only register fields; immediates and
memory offsets are architectural values and are left unchanged.
-/

namespace Flapjack.RiscV

def relabelInstruction (instruction : Instruction width) : Instruction width :=
  match instruction with
  | .add d l r => .add (riscvForward d) (riscvForward l) (riscvForward r)
  | .sub d l r => .sub (riscvForward d) (riscvForward l) (riscvForward r)
  | .addW d l r => .addW (riscvForward d) (riscvForward l) (riscvForward r)
  | .subW d l r => .subW (riscvForward d) (riscvForward l) (riscvForward r)
  | .and d l r => .and (riscvForward d) (riscvForward l) (riscvForward r)
  | .or d l r => .or (riscvForward d) (riscvForward l) (riscvForward r)
  | .xor d l r => .xor (riscvForward d) (riscvForward l) (riscvForward r)
  | .addi d s i => .addi (riscvForward d) (riscvForward s) i
  | .addiW d s i => .addiW (riscvForward d) (riscvForward s) i
  | .andi d s i => .andi (riscvForward d) (riscvForward s) i
  | .ori d s i => .ori (riscvForward d) (riscvForward s) i
  | .xori d s i => .xori (riscvForward d) (riscvForward s) i
  | .mul d l r => .mul (riscvForward d) (riscvForward l) (riscvForward r)
  | .mulW d l r => .mulW (riscvForward d) (riscvForward l) (riscvForward r)
  | .mulHU d l r => .mulHU (riscvForward d) (riscvForward l) (riscvForward r)
  | .sll d l r => .sll (riscvForward d) (riscvForward l) (riscvForward r)
  | .srl d l r => .srl (riscvForward d) (riscvForward l) (riscvForward r)
  | .sra d l r => .sra (riscvForward d) (riscvForward l) (riscvForward r)
  | .sllW d l r => .sllW (riscvForward d) (riscvForward l) (riscvForward r)
  | .srlW d l r => .srlW (riscvForward d) (riscvForward l) (riscvForward r)
  | .sraW d l r => .sraW (riscvForward d) (riscvForward l) (riscvForward r)
  | .slli d s a => .slli (riscvForward d) (riscvForward s) a
  | .srli d s a => .srli (riscvForward d) (riscvForward s) a
  | .srai d s a => .srai (riscvForward d) (riscvForward s) a
  | .slliW d s a => .slliW (riscvForward d) (riscvForward s) a
  | .srliW d s a => .srliW (riscvForward d) (riscvForward s) a
  | .sraiW d s a => .sraiW (riscvForward d) (riscvForward s) a
  | .slt d l r => .slt (riscvForward d) (riscvForward l) (riscvForward r)
  | .slti d s i => .slti (riscvForward d) (riscvForward s) i
  | .sltu d l r => .sltu (riscvForward d) (riscvForward l) (riscvForward r)
  | .sltiu d s i => .sltiu (riscvForward d) (riscvForward s) i
  | .lui d i => .lui (riscvForward d) i
  | .auipc d i => .auipc (riscvForward d) i
  | .divU d l r => .divU (riscvForward d) (riscvForward l) (riscvForward r)
  | .remU d l r => .remU (riscvForward d) (riscvForward l) (riscvForward r)
  | .branchEq l r o => .branchEq (riscvForward l) (riscvForward r) o
  | .branchNe l r o => .branchNe (riscvForward l) (riscvForward r) o
  | .branchLt l r o => .branchLt (riscvForward l) (riscvForward r) o
  | .branchGe l r o => .branchGe (riscvForward l) (riscvForward r) o
  | .branchLtU l r o => .branchLtU (riscvForward l) (riscvForward r) o
  | .branchGeU l r o => .branchGeU (riscvForward l) (riscvForward r) o
  | .jal d o => .jal (riscvForward d) o
  | .jalr d s o => .jalr (riscvForward d) (riscvForward s) o
  | .ecall => .ecall
  | .loadByte d a => .loadByte (riscvForward d) (riscvForward a)
  | .loadByteSigned d a => .loadByteSigned (riscvForward d) (riscvForward a)
  | .storeByte s a => .storeByte (riscvForward s) (riscvForward a)
  | .loadHalf d a => .loadHalf (riscvForward d) (riscvForward a)
  | .loadHalfSigned d a => .loadHalfSigned (riscvForward d) (riscvForward a)
  | .storeHalf s a => .storeHalf (riscvForward s) (riscvForward a)
  | .load32 d a => .load32 (riscvForward d) (riscvForward a)
  | .store32 s a => .store32 (riscvForward s) (riscvForward a)
  | .loadWord d a => .loadWord (riscvForward d) (riscvForward a)
  | .storeWord s a => .storeWord (riscvForward s) (riscvForward a)

@[simp] theorem relabelInstruction_ecall :
    relabelInstruction (.ecall : Instruction width) = .ecall := rfl

@[simp] theorem relabelInstruction_add (width : Nat) (destination sourceLeft sourceRight : Fin 32) :
    relabelInstruction (.add destination sourceLeft sourceRight : Instruction width) =
      .add (riscvForward destination) (riscvForward sourceLeft)
        (riscvForward sourceRight) := rfl

end Flapjack.RiscV
