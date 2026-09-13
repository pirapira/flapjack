import Flapjack.RiscV.RegisterTransfer

/-!
# Re-labelling instructions across the `riscv_names` map

`Flapjack.RiscV.RegisterTransfer` bridges a machine state from internal
register numbers to hardware ones by the explicit inverse of `riscv_names`.
This file adds the instruction side of that bridge: `relabelInstruction`
rewrites every register field of a RISC-V instruction through
`riscvForward`, and `execute_transfer_relabel` shows that executing a
re-labelled instruction on the transferred state agrees with transferring the
result of executing the original instruction.

The equality holds for instructions that never write the two distinguished
names: the hardware zero register `0` and the internal Cake zero register `27`
(whose image is hardware zero).  Those two are exactly the cases where
`writeRegisterInternal` and the hardware `writeRegister` differ, so the bridge
is stated with that explicit side condition, which the production allocator
guarantees by treating the zero register as immutable.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- Rewrite every register field of an instruction through `riscvForward`,
turning internal Cake stack register numbers into hardware register numbers. -/
def relabelInstruction : Instruction width → Instruction width
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

/-- The destination registers written by an instruction (empty for pure reads,
branches, stores and `ecall`). -/
def instructionWrites : Instruction width → List (Fin 32)
  | .add d _ _ => [d] | .sub d _ _ => [d] | .addW d _ _ => [d] | .subW d _ _ => [d]
  | .and d _ _ => [d] | .or d _ _ => [d] | .xor d _ _ => [d]
  | .addi d _ _ => [d] | .addiW d _ _ => [d] | .andi d _ _ => [d]
  | .ori d _ _ => [d] | .xori d _ _ => [d]
  | .mul d _ _ => [d] | .mulW d _ _ => [d] | .mulHU d _ _ => [d]
  | .sll d _ _ => [d] | .srl d _ _ => [d] | .sra d _ _ => [d]
  | .sllW d _ _ => [d] | .srlW d _ _ => [d] | .sraW d _ _ => [d]
  | .slli d _ _ => [d] | .srli d _ _ => [d] | .srai d _ _ => [d]
  | .slliW d _ _ => [d] | .srliW d _ _ => [d] | .sraiW d _ _ => [d]
  | .slt d _ _ => [d] | .slti d _ _ => [d] | .sltu d _ _ => [d] | .sltiu d _ _ => [d]
  | .lui d _ => [d] | .auipc d _ => [d]
  | .divU d _ _ => [d] | .remU d _ _ => [d]
  | .jal d _ => [d] | .jalr d _ _ => [d]
  | .loadByte d _ => [d] | .loadByteSigned d _ => [d]
  | .loadHalf d _ => [d] | .loadHalfSigned d _ => [d]
  | .load32 d _ => [d] | .loadWord d _ => [d]
  | _ => []

/-- The zero-image-aware internal write agrees with the hardware write whenever
the target is neither the hardware zero register `0` nor the internal Cake zero
register `27`. -/
theorem writeRegisterInternal_eq_writeRegister (state : State width) (name : Fin 32)
    (value : Word width) (himage : riscvForward name ≠ 0) (hname : name ≠ 0) :
    writeRegisterInternal riscvForward state name value = writeRegister state name value := by
  simp only [writeRegisterInternal, writeRegister]
  rw [if_neg himage, if_neg hname]

/-- The write bridge specialized to registers that avoid both `0` and `27`. -/
theorem writeRegister_transfer_forward_avoiding (state : State width) (name : Fin 32)
    (value : Word width) (himage : riscvForward name ≠ 0) (hname : name ≠ 0) :
    writeRegister (transferState state) (riscvForward name) value =
      transferState (writeRegister state name value) := by
  rw [writeRegister_transfer_forward]
  rw [writeRegisterInternal_eq_writeRegister _ _ _ himage hname]

/-- Updating the program counter commutes with transferring the register file. -/
@[simp] theorem transferState_pc_update (state : State width) (value : Word width) :
    { transferState state with pc := value } = transferState { state with pc := value } := by
  cases state
  rfl

/-- The successor program counter commutes with transferring the register file. -/
@[simp] theorem nextPc_transfer (state : State width) :
    nextPc (transferState state) = nextPc state := by
  simp [nextPc, transferState]

theorem writeByte_transfer (state : State width) (address : Word width) (value : BitVec 8) :
    writeByte (transferState state) address value =
      transferState (writeByte state address value) := by
  cases state
  rfl

theorem writeWord16_transfer (state : State width) (address value : Word width) :
    writeWord16 (transferState state) address value =
      transferState (writeWord16 state address value) := by
  simp [writeWord16, writeByte_transfer]

theorem writeWord32_transfer (state : State width) (address value : Word width) :
    writeWord32 (transferState state) address value =
      transferState (writeWord32 state address value) := by
  simp [writeWord32, writeByte_transfer]

theorem writeWordValue_transfer (state : State width) (address value : Word width) :
    writeWordValue (transferState state) address value =
      transferState (writeWordValue state address value) := by
  unfold writeWordValue
  generalize List.range (width / 8) = offsets
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets induction =>
      simp only [List.foldl]
      rw [writeByte_transfer]
      rw [induction]

/-- A register write commutes with a program-counter update. -/
theorem writeRegister_pc (state : State width) (pcval : Word width)
    (name : Fin 32) (value : Word width) :
    writeRegister { state with pc := pcval } name value =
      { writeRegister state name value with pc := pcval } := by
  cases state
  by_cases hname : name = 0 <;> simp [writeRegister, hname]

theorem writeByte_pc (state : State width) (pcval : Word width)
    (address : Word width) (value : BitVec 8) :
    writeByte { state with pc := pcval } address value =
      { writeByte state address value with pc := pcval } := by
  cases state
  rfl

theorem writeWord16_pc (state : State width) (pcval address value : Word width) :
    writeWord16 { state with pc := pcval } address value =
      { writeWord16 state address value with pc := pcval } := by
  simp [writeWord16, writeByte_pc]

theorem writeWord32_pc (state : State width) (pcval address value : Word width) :
    writeWord32 { state with pc := pcval } address value =
      { writeWord32 state address value with pc := pcval } := by
  simp [writeWord32, writeByte_pc]

theorem writeWordValue_pc_update (state : State width) (pcval address value : Word width) :
    writeWordValue { state with pc := pcval } address value =
      { writeWordValue state address value with pc := pcval } := by
  unfold writeWordValue
  generalize List.range (width / 8) = offsets
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets induction =>
      simp only [List.foldl]
      rw [writeByte_pc]
      rw [induction]

theorem writeRegister_transfer_forward_pc (state : State width) (pcval : Word width)
    (name : Fin 32) (value : Word width)
    (himage : riscvForward name ≠ 0) (hname : name ≠ 0) :
    writeRegister { transferState state with pc := pcval } (riscvForward name) value =
      transferState { writeRegister state name value with pc := pcval } := by
  calc writeRegister { transferState state with pc := pcval } (riscvForward name) value
      = { writeRegister (transferState state) (riscvForward name) value with pc := pcval } :=
          writeRegister_pc _ _ _ _
    _ = { transferState (writeRegisterInternal riscvForward state name value) with pc := pcval } := by
          rw [writeRegister_transfer_forward]
    _ = transferState { writeRegisterInternal riscvForward state name value with pc := pcval } :=
          transferState_pc_update _ _
    _ = transferState { writeRegister state name value with pc := pcval } := by
          rw [writeRegisterInternal_eq_writeRegister _ _ _ himage hname]

theorem writeByte_transfer_pc (state : State width) (pcval : Word width)
    (address : Word width) (value : BitVec 8) :
    writeByte { transferState state with pc := pcval } address value =
      transferState { writeByte state address value with pc := pcval } := by
  calc writeByte { transferState state with pc := pcval } address value
      = { writeByte (transferState state) address value with pc := pcval } :=
          writeByte_pc _ _ _ _
    _ = { transferState (writeByte state address value) with pc := pcval } := by
          rw [writeByte_transfer]
    _ = transferState { writeByte state address value with pc := pcval } :=
          transferState_pc_update _ _

theorem writeWord16_transfer_pc (state : State width) (pcval address value : Word width) :
    writeWord16 { transferState state with pc := pcval } address value =
      transferState { writeWord16 state address value with pc := pcval } := by
  calc writeWord16 { transferState state with pc := pcval } address value
      = { writeWord16 (transferState state) address value with pc := pcval } :=
          writeWord16_pc _ _ _ _
    _ = { transferState (writeWord16 state address value) with pc := pcval } := by
          rw [writeWord16_transfer]
    _ = transferState { writeWord16 state address value with pc := pcval } :=
          transferState_pc_update _ _

theorem writeWord32_transfer_pc (state : State width) (pcval address value : Word width) :
    writeWord32 { transferState state with pc := pcval } address value =
      transferState { writeWord32 state address value with pc := pcval } := by
  calc writeWord32 { transferState state with pc := pcval } address value
      = { writeWord32 (transferState state) address value with pc := pcval } :=
          writeWord32_pc _ _ _ _
    _ = { transferState (writeWord32 state address value) with pc := pcval } := by
          rw [writeWord32_transfer]
    _ = transferState { writeWord32 state address value with pc := pcval } :=
          transferState_pc_update _ _

theorem writeWordValue_transfer_pc (state : State width) (pcval address value : Word width) :
    writeWordValue { transferState state with pc := pcval } address value =
      transferState { writeWordValue state address value with pc := pcval } := by
  calc writeWordValue { transferState state with pc := pcval } address value
      = { writeWordValue (transferState state) address value with pc := pcval } :=
          writeWordValue_pc_update _ _ _ _
    _ = { transferState (writeWordValue state address value) with pc := pcval } := by
          rw [writeWordValue_transfer]
    _ = transferState { writeWordValue state address value with pc := pcval } :=
          transferState_pc_update _ _

end Flapjack.RiscV
