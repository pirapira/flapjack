import Flapjack.RiscV.Lab
import Flapjack.RiscV.LabDiagnostics

namespace Flapjack.RiscV

example :
    compileLabSectionChecked (width := 64) { services := [] }
      ⟨7, [.labAsm (.heapAlloc 3) [] 0]⟩ =
      .error { sectionId := 7, position := 0, feature := .heapAlloc } := by
  rfl

example :
    compileLabSectionChecked (width := 64) { services := [] }
      ⟨8, [.labAsm (.install : LabAsm (Word 64)) [] 0]⟩ =
      .ok [.jal 0 (0 - BitVec.ofNat 64 32)] := by
  rfl

example :
    compileLabSectionChecked (width := 64) { services := [] }
      ⟨8, [.asm (.tick : LabPlain (Word 64)) [] 0,
        .labAsm (.install : LabAsm (Word 64)) [] 0]⟩ =
      .ok [.jal 0 (0 - BitVec.ofNat 64 32)] := by
  rfl

example :
    compileLabSectionChecked (width := 64) { services := [] }
      ⟨9, [.labAsm (.halt : LabAsm (Word 64)) [] 0]⟩ =
      .ok [.jal 0 (0 - BitVec.ofNat 64 16)] := by
  rfl

def stackRemoveRiscVConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def wordStackRiscVConfig : WordStackConfig :=
  { locations := [(0, .register 4)], scratch := 31, stackBase := 21 }

def wordFfiRiscVConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7)]
    scratch := 31
    stackBase := 21 }

example :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.jal 0 (0 - BitVec.ofNat 64 48)] := by
  decide

example :
    labLineInstructionCount
        (.labAsm (.jump ⟨2, 4⟩) [] 0 : LabLine (Word 64)) = 1 := by
  rfl

example :
    labOffset (width := 64) 12 20 = 0 - BitVec.ofNat 64 8 := by
  rfl

example :
    compileLabProgram (width := 64) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
      some [.jal 0 (BitVec.ofNat 64 4),
        .ori 1 0 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileStackProgramNatListToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.call none (.label 2) none : StackProg Nat)),
       (2, .const 1 7)] =
      some [.jal 0 (BitVec.ofNat 64 4),
        .ori 1 0 (BitVec.ofNat 64 7)] := by
  decide +kernel

example :
    compileStackProgramNatListLinkedToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.const 1 7 : StackProg Nat))] =
      some [(1, BitVec.ofNat 64 0, [.ori 1 0 (BitVec.ofNat 64 7)])] := by
  decide +kernel

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .add 4 5 6) [] 0]⟩ =
      some [.add 4 5 6] := by
  decide

/- Cake's `riscv_bop_r` table also maps register `Sub`, `And`, and `Or`
   directly to their RISC-V R-type instructions.  Keep these distinct from
   the immediate and Word-level guards below. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .sub 4 5 6) [] 0]⟩ =
      some [.sub 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .and 4 5 6) [] 0]⟩ =
      some [.and 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .or 4 5 6) [] 0]⟩ =
      some [.or 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .sub 20 20 16) [] 0]⟩ =
      some [.addi 20 20 (0 - BitVec.ofNat 64 16)] := by
  decide

/- Cake's `riscv_target` accepts exactly the signed-12 arithmetic immediate
   interval.  Pin both endpoints at the Lab boundary so a future change to
   immediate normalization cannot alter the emitted ADDI bytes. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .add 20 20 2047) [] 0]⟩ =
      some [.addi 20 20 (BitVec.ofNat 64 2047)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .sub 20 20 2048) [] 0]⟩ =
      some [.addi 20 20 (0 - BitVec.ofNat 64 2048)] := by
  decide

/- CakeML's final Lab filter removes arithmetic identities, including the
   zero-immediate forms that can arise from a fused stack-pointer update. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .add 20 20 0) [] 0]⟩ =
      some [] := by
  decide

example :
    labLineInstructionCount
        (.asm (.arithImm .sub 20 20 0) [] 0 : LabLine (Word 64)) = 0 := by
  rfl

/- Cake's Word arithmetic rotate expansion occupies three instructions for
   an immediate amount and five for a register amount.  These counts are also
   used to place cross-section labels in the linked artifact. -/
example :
    (labLineInstructionCount
        (.asm (.word (.arith (.shift .ror 10 1
          (.imm (BitVec.ofNat 64 2))))) [] 0 : LabLine (Word 64))) = 3 := by
  rfl

example :
    (labLineInstructionCount
        (.asm (.word (.arith (.shift .ror 10 1
          (.reg 2)))) [] 0 : LabLine (Word 64))) = 5 := by
  rfl

/- The direct Word arithmetic boundary must preserve Cake's immediate rotate
   expansion, not merely its retained instruction count. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .ror 4 5
        (.imm (BitVec.ofNat 64 3))))) [] 0]⟩ =
      some [
        .srli 31 5 (BitVec.ofNat 64 3),
        .slli 4 5 (BitVec.ofNat 64 61),
        .or 4 4 31] := by
  decide

/- Cake's variable Word rotate-right keeps the five-instruction temporary
   sequence at the list-valued arithmetic boundary. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .ror 4 5 (.reg 6)))) [] 0]⟩ =
      some [
        .ori 31 0 (BitVec.ofNat 64 64),
        .sub 31 31 6,
        .sll 31 5 31,
        .srl 4 5 6,
        .or 4 4 31] := by
  decide

/- Cake's list-valued Word arithmetic keeps an immediate arithmetic shift as
   one target shift instruction; pin all three `riscv_sh` mappings. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .lsl 4 5
        (.imm (BitVec.ofNat 64 7))))) [] 0]⟩ =
      some [.slli 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .lsr 4 5
        (.imm (BitVec.ofNat 64 7))))) [] 0]⟩ =
      some [.srli 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .asr 4 5
        (.imm (BitVec.ofNat 64 7))))) [] 0]⟩ =
      some [.srai 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.codeBufferWrite 7 6) [] 0]⟩ =
      some [.storeByte 6 7] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.dataBufferWrite 7 6) [] 0]⟩ =
      some [.storeWord 6 7] := by
  decide

/-! CakeML's constant encoder uses LUI plus a signed low-immediate operation
    once a constant no longer fits the 12-bit ORI case. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0x40000008) [] 0]⟩ =
      some [.lui 1 (BitVec.ofNat 64 0x40000),
        .addi 1 1 (BitVec.ofNat 64 8)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0x100000000) [] 0]⟩ =
      some [.lui 31 0, .addi 31 31 0,
        .lui 1 0, .addi 1 1 1,
        .slli 1 1 (BitVec.ofNat 64 32), .or 1 1 31] := by
  decide

/-! These cases exercise the sign-aware branches of CakeML's `riscv_ast
    (Const ...)`: a value with bit 31 set is still a positive RV64 value and
    therefore needs the two-half XOR sequence, while all ones fits the signed
    12-bit ORI case after sign extension. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0xa0010000) [] 0]⟩ =
      some [.lui 31 (BitVec.ofNat 64 0xa0010), .addi 31 31 0,
        .lui 1 0, .xori 1 1 (BitVec.ofNat 64 0xfff),
        .slli 1 1 (BitVec.ofNat 64 32), .xor 1 1 31] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0xffffffffffffffff) [] 0]⟩ =
      some [.ori 1 0 (BitVec.ofNat 64 0xfff)] := by
  decide

example :
    labLineInstructionCount
        (.asm (.const 1 0x40000008) [] 0 : LabLine (Word 64)) = 2 := by
  rfl

example :
    labLineInstructionCount
        (.asm (.const 1 0x100000000) [] 0 : LabLine (Word 64)) = 6 := by
  rfl

def haltLabProgram : LabProgram (Word 64) :=
  [⟨1, [.labAsm (.halt : LabAsm (Word 64)) [] 0]⟩]

-- `LabAsm.halt` lowers to a backward jump into the linked runtime halt
-- region, which is not part of a bare program; the standalone model
-- therefore never reaches the synthetic end-of-program halt.
example :
    (executeLabProgramWithHalt 10 { services := [] } haltLabProgram
      (zeroState 64)).map (fun state => state.pc) =
      none := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shift .lsl 4 5 6) [] 0]⟩ =
      some [.sll 4 5 6] := by
  decide

/- Cake's register-variable shifts use the target SLL/SRL/SRA equations from
   riscv_targetScript.sml, distinct from the immediate shift cases above. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .lsl 4 5 (.reg 6)))) [] 0]⟩ =
      some [.sll 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .lsr 4 5 (.reg 6)))) [] 0]⟩ =
      some [.srl 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.shift .asr 4 5 (.reg 6)))) [] 0]⟩ =
      some [.sra 4 5 6] := by
  decide

/- Cake's direct register Binop boundary emits the corresponding RISC-V
   register ALU instruction without an intermediate materialization. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .xor 4 5 6) [] 0]⟩ =
      some [.xor 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longMul 4 5 6 7))) [] 0]⟩ =
      some [.mulHU 4 6 7, .mul 5 6 7] := by
  decide

/- Cake rejects a LongMul when its high-result destination aliases either
   source; the helper expansion is only valid after this source-boundary check. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longMul 6 5 6 7))) [] 0]⟩ = none := by
  decide

/- Cake's register binary subtraction lowers directly to the RV64 SUB row;
   keep the register carrier distinct from the immediate ADDI form above. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.binOp .sub 4 5 (.reg 6)))) [] 0]⟩ =
      some [.sub 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.binOp .and 4 5 (.reg 6)))) [] 0]⟩ =
      some [.and 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.binOp .or 4 5 (.reg 6)))) [] 0]⟩ =
      some [.or 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.binOp .xor 4 5 (.reg 6)))) [] 0]⟩ =
      some [.xor 4 5 6] := by
  decide

/- Cake's `riscv_ast (Inst (Arith (Div ...)))` selects the signed RISC-V
   DIV encoding.  Flapjack's historical constructor is named `divU`, but its
   encoder uses Cake's funct3=4/funct7=1 row; pin that source-shaped Lab
   boundary explicitly so the name cannot hide a DIVU regression. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.div 4 5 6))) [] 0]⟩ =
      some [.divU 4 5 6] := by
  decide

/- Cake's direct RISC-V target rejects `LongDiv`; the Pancake runtime helper
   is inserted earlier by the Stack pipeline, so Lab must not silently emit a
   target instruction for an unexpanded LongDiv node. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longDiv 4 5 6 7 8))) [] 0]⟩ = none := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.addCarry 4 5 6 7 8))) [] 0]⟩ =
      some [.sltu 31 0 8, .add 4 6 7, .sltu 5 4 7,
        .add 4 4 31, .sltu 31 4 31, .or 5 5 31] := by
  decide

/- Cake's four-register AddCarry carrier uses the carry register as both
   input and output, unlike Pancake's five-register primitive above. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.cakeAddCarry 4 6 7 8))) [] 0]⟩ =
      some [.sltu 31 0 8, .add 4 6 7, .sltu 8 4 7,
        .add 4 4 31, .sltu 31 4 31, .or 8 8 31] := by
  decide

/- Cake's four-register AddCarry is distinct from Pancake's five-register
   two-result carrier; pin its direct target expansion separately. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.cakeAddCarry 4 5 6 7))) [] 0]⟩ =
      some [.sltu 31 0 7, .add 4 5 6, .sltu 7 4 6,
        .add 4 4 31, .sltu 31 4 31, .or 7 7 31] := by
  decide

/- Cake's list-valued Word `Binop` carrier preserves a register right
   operand as one target ALU instruction. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.binOp .and 4 5 (.reg 6)))) [] 0]⟩ =
      some [.and 4 5 6] := by
  decide

/- Cake's list-valued Word `Binop Sub` carrier keeps an immediate operand in
   the I-format signed-negation form rather than treating it as a register. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith
        (.binOp .sub 4 5 (.imm (BitVec.ofNat 64 24))))) [] 0]⟩ =
      some [.addi 4 5 (0 - BitVec.ofNat 64 24)] := by
  decide

/- Cake's `riscv_ast` immediate-Binop rule maps `Add` through
   `riscv_bop_i Add = ADDI`; keep this distinct from the signed-negation
   `Sub` case above (riscv_targetScript.sml:47-51, 117-120). -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith
        (.binOp .add 4 5 (.imm (BitVec.ofNat 64 24))))) [] 0]⟩ =
      some [.addi 4 5 (BitVec.ofNat 64 24)] := by
  decide

/- Cake's `riscv_bop_i` table applies the same immediate-carrier boundary to
   the remaining logical binary operators; keep these distinct from the
   direct `arithImm` constructors above. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith
        (.binOp .and 4 5 (.imm (BitVec.ofNat 64 24))))) [] 0]⟩ =
      some [.andi 4 5 (BitVec.ofNat 64 24)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith
        (.binOp .or 4 5 (.imm (BitVec.ofNat 64 24))))) [] 0]⟩ =
      some [.ori 4 5 (BitVec.ofNat 64 24)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith
        (.binOp .xor 4 5 (.imm (BitVec.ofNat 64 24))))) [] 0]⟩ =
      some [.xori 4 5 (BitVec.ofNat 64 24)] := by
  decide

/- Cake's `riscv_ast (Inst (Arith (Div ...)))` reaches the target DIV
   encoding through the direct Lab word-arithmetic boundary. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.div 4 5 6))) [] 0]⟩ =
      some [.divU 4 5 6] := by
  decide

/- Cake's riscv_targetScript.sml maps direct `LongDiv` to
   riscv_encode_fail; the Lab arithmetic boundary preserves that rejection. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longDiv 4 5 6 7 8))) [] 0]⟩ =
      none := by
  decide

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.get 4 .heapLength : StackProg (Word 64)) =
      some [
        .loadWordOffset 4 10 (0 - BitVec.ofNat 64 24)] := by
  decide +kernel

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.dataBufferWrite 7 6 : StackProg (Word 64)) =
      some [.storeWord 6 7] := by
  decide +kernel

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.codeBufferWrite 7 6 : StackProg (Word 64)) =
      some [.storeByte 6 7] := by
  decide +kernel

example :
    (compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.storeConsts 6 7 none : StackProg (Word 64))).isSome := by
  decide +kernel

example :
    compileWordProgramNatToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const 42) : WordProg Nat) =
      some [.ori 4 0 (BitVec.ofNat 64 42)] := by
  decide +kernel

example :
    compileWordProgramToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const (BitVec.ofNat 64 42)) : WordProg (Word 64)) =
      some [.ori 4 0 (BitVec.ofNat 64 42)] := by
  decide +kernel

example :
    compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } wordFfiRiscVConfig
      stackRemoveRiscVConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat) =
      some [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
        .auipc 1 (BitVec.ofNat 64 0),
        .addi 1 1 (BitVec.ofNat 64 12),
        .jal 0 (0 - BitVec.ofNat 64 72)] := by
  decide +kernel

example :
    labLineInstructionCount
        (.asm (.shift .ror 4 5 6) [] 0 : LabLine (Word 64)) = 5 := by
  rfl

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shift .ror 4 5 6) [] 0]⟩ =
      some [
        .ori 31 0 (BitVec.ofNat 64 64),
        .sub 31 31 6,
        .sll 31 5 31,
        .srl 4 5 6,
        .or 4 4 31] := by
  decide

/- Cake's RV64 target has no RORI instruction.  A rotate with a constant
   amount is the same three-instruction `riscv_ast` expansion as the Word
   backend; the Lab path must not reject the fused StackRemove form. -/
example :
    labLineInstructionCount
        (.asm (.shiftImm .ror 4 5 3) [] 0 : LabLine (Word 64)) = 3 := by
  rfl

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shiftImm .ror 4 5 3) [] 0]⟩ =
      some [
        .srli 31 5 (BitVec.ofNat 64 3),
        .slli 4 5 (BitVec.ofNat 64 61),
        .or 4 4 31] := by
  decide

/-! Cake's `riscv_ast (Inst (Mem mop r1 (Addr r2 a)))` supports every
    `WordMemOp`, including the narrow and unsigned-width operations.  The
    compatibility `stackMem` Lab constructors must preserve those target
    encodings instead of silently returning `none`. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load8 4 5 7) [] 0]⟩ =
      some [.loadByteOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

/-! The direct Cake `Mem ... (Addr ...)` path uses the same `riscv_memop`
    table as shared memory, but these word-width and halfword-width forms are
    distinct from the shared-memory table above.  Pin both signed directions
    at the Lab boundary against `riscv_targetScript.sml:66-74, 165-169`. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load 4 5 7) [] 0]⟩ =
      some [.loadWordOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store 4 5 7) [] 0]⟩ =
      some [.storeWordOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store 4 5 7) [] 0]⟩ =
      some [.storeWordOffset 4 5 (0 - BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load 4 5 7) [] 0]⟩ =
      some [.loadWordOffset 4 5 (0 - BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load16 4 5 7) [] 0]⟩ =
      some [.loadHalfOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

/- The positive `Addr` carrier uses the same Cake width table for stores;
   pin the byte and halfword store rows separately from the load rows above. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store8 4 5 7) [] 0]⟩ =
      some [.storeByteOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store16 4 5 7) [] 0]⟩ =
      some [.storeHalfOffset 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store16 4 5 7) [] 0]⟩ =
      some [.storeHalfOffset 4 5 (0 - BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store32 4 5 7) [] 0]⟩ =
      some [.store32Offset 4 5 (0 - BitVec.ofNat 64 7)] := by
  decide

/- The same Cake `Addr` lowering preserves a negative halfword displacement
   for the subtracting carrier, including the signed target encoding. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load16 4 5 9) [] 0]⟩ =
      some [.loadHalfOffset 4 5 (0 - BitVec.ofNat 64 9)] := by
  decide

/- The subtracting `Addr` carrier preserves the signed displacement for
   byte and unsigned-word loads as well. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load8 4 5 9) [] 0]⟩ =
      some [.loadByteOffset 4 5 (0 - BitVec.ofNat 64 9)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load32 4 5 9) [] 0]⟩ =
      some [.load32Offset 4 5 (0 - BitVec.ofNat 64 9)] := by
  decide

/- A positive signed-12 boundary remains an offset instruction; materializing
   it here would diverge from Cake's `riscv_targetScript.sml` Mem encoding. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store32 4 5 2047) [] 0]⟩ =
      some [.store32Offset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

/- Cake preserves the signed displacement for a subtracting byte store too;
   the width-specific target opcode must not erase the negative offset. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store8 4 5 8) [] 0]⟩ =
      some [.storeByteOffset 4 5 (0 - BitVec.ofNat 64 8)] := by
  decide

/- Cake's lower signed-12 endpoint remains a direct width-specific Store;
   the subtracting carrier must encode `-2048`, not materialize the address. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store32 4 5 2048) [] 0]⟩ =
      some [.store32Offset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

/- The matching lower signed-12 Load32 endpoint is also a direct Cake Mem
   carrier; it must retain `-2048` rather than fall back to address synthesis. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load32 4 5 2048) [] 0]⟩ =
      some [.load32Offset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

/- The full-width Cake Word carriers use the same lower signed-12 endpoint;
   retain `-2048` for ordinary Load/Store, not only Load32/Store32. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store 4 5 2048) [] 0]⟩ =
      some [.storeWordOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load 4 5 2048) [] 0]⟩ =
      some [.loadWordOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

/- The same Cake lower signed-12 boundary applies independently to the
   byte/halfword memory-op rows; retain each width-specific target opcode. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load8 4 5 2048) [] 0]⟩ =
      some [.loadByteOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .load16 4 5 2048) [] 0]⟩ =
      some [.loadHalfOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store8 4 5 2048) [] 0]⟩ =
      some [.storeByteOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMemSub .store16 4 5 2048) [] 0]⟩ =
      some [.storeHalfOffset 4 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

/- The largest positive signed-12 displacement remains a direct load32. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load32 4 5 2047) [] 0]⟩ =
      some [.load32Offset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

/- The same Cake signed-12 positive endpoint applies to the remaining
   width-specific memory operations; preserve the target opcode and offset
   together rather than checking only the word-width row. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load8 4 5 2047) [] 0]⟩ =
      some [.loadByteOffset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .load16 4 5 2047) [] 0]⟩ =
      some [.loadHalfOffset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store8 4 5 2047) [] 0]⟩ =
      some [.storeByteOffset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.stackMem .store16 4 5 2047) [] 0]⟩ =
      some [.storeHalfOffset 4 5 (BitVec.ofNat 64 2047)] := by
  decide

/-! Cake's immediate binary operators use the corresponding I-format
    instruction, not a rejected lowering. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.arithImm .and 4 5 7) [] 0]⟩ =
      some [.andi 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.arithImm .or 4 5 7) [] 0]⟩ =
      some [.ori 4 5 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨4, [.asm (.arithImm .xor 4 5 7) [] 0]⟩ =
      some [.xori 4 5 (BitVec.ofNat 64 7)] := by
  decide

/-! GH #1093 (bead flapjack-lhj): end-to-end regression for the `labFlatten`
   `ite` cases — a Stack-level conditional compiled all the way to RISC-V
   must execute the then-branch when the condition holds and the
   else-branch when it does not (previously the general case left the
   then-branch dead, and the skip-then case ran the else-branch on a true
   condition). -/

/-- `if reg4 == 0 then reg1 := 1 else reg1 := 2`, compiled and executed. -/
def labIteGeneralProgram : StackProg (Word 64) :=
  .ite .equal 4 (.imm 0) (.const 1 1) (.const 1 2)

def labIteGeneralCode : Option (List (Instruction 64)) :=
  compileStackProgramToRiscV (width := 64) { services := [] }
    stackRemoveRiscVConfig 2 3 labIteGeneralProgram

-- Condition true: the then-branch runs.
#guard
    labIteGeneralCode.bind (fun code =>
      (executeCode 30 (0 : Word 64) code
        (writeRegister (zeroState 64) 4 0)).map
          (fun state => readRegister state 1)) =
      some (1 : Word 64)

-- Condition false: the else-branch runs.
#guard
    labIteGeneralCode.bind (fun code =>
      (executeCode 30 (0 : Word 64) code
        (writeRegister (zeroState 64) 4 7)).map
          (fun state => readRegister state 1)) =
      some (2 : Word 64)

/-- `if reg4 == 0 then skip else reg1 := 2`, compiled and executed. -/
def labIteSkipThenCode : Option (List (Instruction 64)) :=
  compileStackProgramToRiscV (width := 64) { services := [] }
    stackRemoveRiscVConfig 2 3
    (.ite .equal 4 (.imm 0) .skip (.const 1 2) : StackProg (Word 64))

-- Condition true: the else-branch must NOT run (reg1 keeps its old value).
#guard
    labIteSkipThenCode.bind (fun code =>
      (executeCode 30 (0 : Word 64) code
        (writeRegister (writeRegister (zeroState 64) 4 0) 1 9)).map
          (fun state => readRegister state 1)) =
      some (9 : Word 64)

-- Condition false: the else-branch runs.
#guard
    labIteSkipThenCode.bind (fun code =>
      (executeCode 30 (0 : Word 64) code
        (writeRegister (writeRegister (zeroState 64) 4 7) 1 9)).map
          (fun state => readRegister state 1)) =
      some (2 : Word 64)

/-! Cake's `Addr reg imm` for shared-memory operations (GH #1113 /
    bead flapjack-anb): `word_to_stack$wShareInst` only ever sees
    `Addr ad offset`, so an immediate store offset must collapse into a single
    offset store (`sb rs, imm(rd)`) instead of materialising the address with a
    separate `addi`.  This program is exactly the shape the Word-to-Stack
    lowering emits for `!st8 out + 32, 1` (a `const` scratch plus an `arith`
    staging pair in front of the `shMem`). -/
def labSharedStoreOffsetProgram : StackProg (Word 64) :=
  .seq (.seq (.const 2 32) (.arith .add 2 1 2)) (.shMem .store8 4 2)

def labSharedStoreOffsetCode : Option (List (Instruction 64)) :=
  compileStackProgramToRiscV (width := 64) { services := [] }
    stackRemoveRiscVConfig 2 3 labSharedStoreOffsetProgram

/-- The immediate offset survives as an offset store, not as a `addi`. -/
def labSharedStoreOffsetFused : Bool :=
  labSharedStoreOffsetCode.any (fun code =>
    code.any (fun instruction =>
      match instruction with
      | .storeByteOffset _ _ offset => offset == (32 : Word 64)
      | _ => false))

#guard labSharedStoreOffsetFused

/- Cake's `riscv_memop` table maps every shared-memory offset operator to its
   corresponding RISC-V load/store width (`riscv_targetScript.sml:66-74,
   165-169`).  Keep the complete table checked at the Lab boundary, not just
   the byte-store case above. -/
def sharedMemOffsetOperatorTable : Bool :=
  [
    labCompilePlain (width := 64)
      (.shareMemOffset .load 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .store 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .load8 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .store8 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .load16 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .store16 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .load32 10 11 (BitVec.ofNat 64 32)),
    labCompilePlain (width := 64)
      (.shareMemOffset .store32 10 11 (BitVec.ofNat 64 32))
  ] == [
    some [.loadWordOffset 10 11 (BitVec.ofNat 64 32)],
    some [.storeWordOffset 10 11 (BitVec.ofNat 64 32)],
    some [.loadByteOffset 10 11 (BitVec.ofNat 64 32)],
    some [.storeByteOffset 10 11 (BitVec.ofNat 64 32)],
    some [.loadHalfOffset 10 11 (BitVec.ofNat 64 32)],
    some [.storeHalfOffset 10 11 (BitVec.ofNat 64 32)],
    some [.load32Offset 10 11 (BitVec.ofNat 64 32)],
    some [.store32Offset 10 11 (BitVec.ofNat 64 32)]
  ]

#guard sharedMemOffsetOperatorTable

/- The shared-memory Cake path uses the same signed-12 endpoint as the
   stack-memory path, but it is a separate `shareMemOffset` carrier.  Pin the
   narrow rows here so the shared-memory encoder cannot regress independently. -/
example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load8 10 11 (BitVec.ofNat 64 2047)) =
      some [.loadByteOffset 10 11 (BitVec.ofNat 64 2047)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load16 10 11 (BitVec.ofNat 64 2047)) =
      some [.loadHalfOffset 10 11 (BitVec.ofNat 64 2047)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store8 10 11 (BitVec.ofNat 64 2047)) =
      some [.storeByteOffset 10 11 (BitVec.ofNat 64 2047)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store16 10 11 (BitVec.ofNat 64 2047)) =
      some [.storeHalfOffset 10 11 (BitVec.ofNat 64 2047)] := by
  decide

/- Cake's shared-memory carrier also preserves a wrapped negative displacement;
   the target sees `2^64 - 8` as signed `-8` for each narrow opcode. -/
example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load8 10 11 (BitVec.ofNat 64 (2 ^ 64 - 8))) =
      some [.loadByteOffset 10 11 (0 - BitVec.ofNat 64 8)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load16 10 11 (BitVec.ofNat 64 (2 ^ 64 - 8))) =
      some [.loadHalfOffset 10 11 (0 - BitVec.ofNat 64 8)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store8 10 11 (BitVec.ofNat 64 (2 ^ 64 - 8))) =
      some [.storeByteOffset 10 11 (0 - BitVec.ofNat 64 8)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store16 10 11 (BitVec.ofNat 64 (2 ^ 64 - 8))) =
      some [.storeHalfOffset 10 11 (0 - BitVec.ofNat 64 8)] := by
  decide

/- The full-width shared-memory carriers retain Cake's lower signed-12
   endpoint as direct offset instructions, independently of the narrow rows. -/
example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load 10 11 (BitVec.ofNat 64 (2 ^ 64 - 2048))) =
      some [.loadWordOffset 10 11 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store 10 11 (BitVec.ofNat 64 (2 ^ 64 - 2048))) =
      some [.storeWordOffset 10 11 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .load32 10 11 (BitVec.ofNat 64 (2 ^ 64 - 2048))) =
      some [.load32Offset 10 11 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompilePlain (width := 64)
      (.shareMemOffset .store32 10 11 (BitVec.ofNat 64 (2 ^ 64 - 2048))) =
      some [.store32Offset 10 11 (0 - BitVec.ofNat 64 2048)] := by
  decide
/- Cake's source-shaped `wordShareInstToInstructionsCake` keeps a variable
   address as one direct `Mem` carrier.  Check every width in the target
   `riscv_memop` table at this backend boundary, independently of the
   stack-shaped offset table above. -/
def cakeWordShareMemOperatorTable : Bool :=
  [
    wordShareInstToInstructionsCake (width := 64) .load 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .store 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .load8 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .store8 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .load16 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .store16 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .load32 10 (.var 11),
    wordShareInstToInstructionsCake (width := 64) .store32 10 (.var 11)
  ] == [
    some [.loadWord 10 11],
    some [.storeWord 10 11],
    some [.loadByte 10 11],
    some [.storeByte 10 11],
    some [.loadHalf 10 11],
    some [.storeHalf 10 11],
    some [.load32 10 11],
    some [.store32 10 11]
  ]

#guard cakeWordShareMemOperatorTable

/- Cake's direct `Mem` address form preserves a subtractive displacement as a
   signed RISC-V offset while retaining the selected store width. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.memOffset .store32 .sub 4 10 24) [] 0]⟩ =
      some [.store32Offset 4 10 (0 - BitVec.ofNat 64 24)] := by
  decide

/- Cake's direct `Mem (Addr ...)` carrier uses the complete `riscv_memop`
   table for a positive displacement as well.  Keep this separate from the
   source-shaped shared-memory and stack-memory tables above: it exercises the
   `WordInst.memOffset` Lab boundary that feeds the target encoder directly. -/
def memOffsetOperatorTable : Bool :=
  [
    labCompilePlain (width := 64)
      (.memOffset .load .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .store .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .load8 .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .store8 .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .load16 .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .store16 .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .load32 .add 4 10 24),
    labCompilePlain (width := 64)
      (.memOffset .store32 .add 4 10 24)
  ] == [
    some [.loadWordOffset 4 10 (BitVec.ofNat 64 24)],
    some [.storeWordOffset 4 10 (BitVec.ofNat 64 24)],
    some [.loadByteOffset 4 10 (BitVec.ofNat 64 24)],
    some [.storeByteOffset 4 10 (BitVec.ofNat 64 24)],
    some [.loadHalfOffset 4 10 (BitVec.ofNat 64 24)],
    some [.storeHalfOffset 4 10 (BitVec.ofNat 64 24)],
    some [.load32Offset 4 10 (BitVec.ofNat 64 24)],
    some [.store32Offset 4 10 (BitVec.ofNat 64 24)]
  ]

#guard memOffsetOperatorTable

-- reg1 holds the base and reg4 the byte: the store lands at base + 32.
#guard
    labSharedStoreOffsetCode.bind (fun code =>
      (executeCode 30 (0 : Word 64) code
        (writeRegister (writeRegister (zeroState 64) 1 100) 4 7)).map
          (fun state => readByte state 132)) =
      some (7 : Word 8)

/-! GH #1053: the RISC-V target uses Cake's direct-JAL and inverted-branch
    fallbacks once a PC-relative target leaves the short encoding range. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4)] 0
      (.jump ⟨1, 0⟩) =
      some [.jal 0 (BitVec.ofNat 64 4)] := by
  decide

/- Cake's `riscv_ast (JumpReg r)` emits the direct zero-link JALR form. -/
example :
    labCompilePlain (width := 64) (.jumpReg 4) =
      some [.jalr 0 4 0] := by
  decide

/- Cake's `Return` carrier is the same `JumpReg` target operation, with
   source register 0 denoting the conventional link register x1. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [] 0 (.return 0) =
      some [.jalr 0 1 0] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [] 0 (.return 4) =
      some [.jalr 0 4 0] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 2 ^ 20)] 0
      (.jump ⟨1, 0⟩) =
      some [.auipc 31 (BitVec.ofNat 64 256),
        .jalr 0 31 (BitVec.ofNat 64 0)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 2 ^ 20)] 0
      (.call ⟨1, 0⟩) =
      some [.auipc 31 (BitVec.ofNat 64 256),
        .jalr 1 31 (BitVec.ofNat 64 0)] := by
  decide

/- Cake's short `Call` form uses the link register x1 in the direct JAL. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4)] 0
      (.call ⟨1, 0⟩) =
      some [.jal 1 (BitVec.ofNat 64 4)] := by
  decide

/- Cake's CallFFI target also takes the AUIPC/JALR fallback when the current
   PC plus the service-stub distance leaves the direct-JAL range. -/
example :
    labCompileAsm (width := 64)
      { services := [("first", 7)] } 1 [] (2 ^ 20)
      (.callFfi "first") =
      some [.auipc 31 (BitVec.ofInt 64 (-256)),
        .jalr 0 31 (BitVec.ofInt 64 (-48))] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 5000)] 0
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchEq 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4996)] := by
  decide

/-! Exact `riscv_targetScript.sml` range boundaries: a forward branch at
    `+0xFFC` remains direct, while `+0x1000` takes the inverted-branch/JAL
    fallback.  Direct JAL remains valid through `2^20 - 2`. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchNe 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchEq 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

/-! Cake inverts the tested relation, not just equality, around the far JAL.
    Pin the direct/far boundary for every ordinary relational comparator. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .notEqual 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchEq 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .notEqual 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchNe 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .less 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchGe 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .less 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchLt 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .lower 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchGeU 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .lower 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchLtU 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .notLess 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchLt 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .notLess 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchGe 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4092)] 0
      (.jumpCmp .notLower 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchLtU 4 5 (BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 0
      (.jumpCmp .notLower 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchGeU 4 5 (BitVec.ofNat 64 8),
        .jal 0 (BitVec.ofNat 64 4092)] := by
  decide

/-! The same five relations with an immediate RHS retain Cake's ORI prelude;
    the direct branch therefore targets `a - 4`, while the far form skips the
    inverted branch and jumps by `a - 8`. -/
private def jumpCmpImmBoundary (operator : Cmp) (target : Nat) :
    Option (List (Instruction 64)) :=
  labCompileAsm (width := 64) { services := [] } 1 [(0, target)] 0
    (.jumpCmp operator 4 (.imm 3) ⟨1, 0⟩)

#guard jumpCmpImmBoundary .notEqual 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchEq 4 31 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .notEqual 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchNe 4 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .less 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchGe 4 31 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .less 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchLt 4 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .lower 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchGeU 4 31 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .lower 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchLtU 4 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .notLess 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchLt 4 31 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .notLess 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchGe 4 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .notLower 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchLtU 4 31 (BitVec.ofNat 64 4088)]
#guard jumpCmpImmBoundary .notLower 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchGeU 4 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 2 ^ 20 - 2)] 0
      (.jump ⟨1, 0⟩) =
      some [.jal 0 (BitVec.ofNat 64 (2 ^ 20 - 2))] := by
  decide

/- The negative JAL boundary is asymmetric in Cake's target encoder: the
   direct form includes -2^20, while the first smaller target requires the
   AUIPC/JALR long-transfer sequence. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] (2 ^ 20)
      (.jump ⟨1, 0⟩) =
      some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] (2 ^ 20 + 2)
      (.jump ⟨1, 0⟩) =
      some [.auipc 31 (BitVec.ofInt 64 (-256)),
        .jalr 0 31 (BitVec.ofInt 64 (-2))] := by
  decide

/-! The matching negative branch boundaries are distinct in Cake's target
    encoder: `-0xFFC` remains a direct branch, while `-0x1000` uses the
    inverted-branch/JAL sequence. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 4092
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchNe 4 5 (0 - BitVec.ofNat 64 4092)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 4096
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchEq 4 5 (BitVec.ofNat 64 8),
        .jal 0 (0 - BitVec.ofNat 64 4100)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 1000)] 0
      (.jumpCmp .equal 4 (.reg 5) ⟨1, 0⟩) =
      some [.branchNe 4 5 (BitVec.ofNat 64 1000)] := by
  decide

/-! GH #1050: `Loc`/`LinkValue` must use Cake's PC-relative AUIPC+ADDI
    sequence, including the signed-low-immediate carry boundary. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4100)] 0
      (.locValue 5 ⟨1, 0⟩) =
      some [.auipc 5 (BitVec.ofNat 64 1),
        .addi 5 5 (BitVec.ofNat 64 4)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 2048)] 0
      (.locValue 5 ⟨1, 0⟩) =
      some [.auipc 5 (BitVec.ofNat 64 1),
        .addi 5 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 4096)] 4
      (.linkValue ⟨1, 0⟩) =
      some [.auipc 1 (BitVec.ofNat 64 1),
        .addi 1 1 (0 - BitVec.ofNat 64 4)] := by
  decide

/- The negative PC-relative side uses the same Cake signed-low carry rule:
   -2048 keeps a zero high word, while -2049 rounds the high word down. -/
example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 2048
      (.locValue 5 ⟨1, 0⟩) =
      some [.auipc 5 (BitVec.ofNat 64 0),
        .addi 5 5 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 2049
      (.locValue 5 ⟨1, 0⟩) =
      some [.auipc 5 (0 - BitVec.ofNat 64 1),
        .addi 5 5 (BitVec.ofNat 64 2047)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 2048
      (.linkValue ⟨1, 0⟩) =
      some [.auipc 1 (BitVec.ofNat 64 0),
        .addi 1 1 (0 - BitVec.ofNat 64 2048)] := by
  decide

example :
    labCompileAsm (width := 64) { services := [] } 1 [(0, 0)] 2049
      (.linkValue ⟨1, 0⟩) =
      some [.auipc 1 (0 - BitVec.ofNat 64 1),
        .addi 1 1 (BitVec.ofNat 64 2047)] := by
  decide

end Flapjack.RiscV
