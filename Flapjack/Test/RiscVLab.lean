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
  native_decide

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
  native_decide

example :
    compileStackProgramNatListToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.call none (.label 2) none : StackProg Nat)),
       (2, .const 1 7)] =
      some [.jal 0 (BitVec.ofNat 64 4),
        .ori 1 0 (BitVec.ofNat 64 7)] := by
  native_decide

example :
    compileStackProgramNatListLinkedToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.const 1 7 : StackProg Nat))] =
      some [(1, BitVec.ofNat 64 0, [.ori 1 0 (BitVec.ofNat 64 7)])] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .add 4 5 6) [] 0]⟩ =
      some [.add 4 5 6] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .sub 20 20 16) [] 0]⟩ =
      some [.addi 20 20 (0 - BitVec.ofNat 64 16)] := by
  native_decide

/- CakeML's final Lab filter removes arithmetic identities, including the
   zero-immediate forms that can arise from a fused stack-pointer update. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arithImm .add 20 20 0) [] 0]⟩ =
      some [] := by
  native_decide

example :
    labLineInstructionCount
        (.asm (.arithImm .sub 20 20 0) [] 0 : LabLine (Word 64)) = 0 := by
  rfl

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.codeBufferWrite 7 6) [] 0]⟩ =
      some [.storeByte 6 7] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.dataBufferWrite 7 6) [] 0]⟩ =
      some [.storeWord 6 7] := by
  native_decide

/-! CakeML's constant encoder uses LUI plus a signed low-immediate operation
    once a constant no longer fits the 12-bit ORI case. -/
example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0x40000008) [] 0]⟩ =
      some [.lui 1 (BitVec.ofNat 64 0x40000),
        .addi 1 1 (BitVec.ofNat 64 8)] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0x100000000) [] 0]⟩ =
      some [.lui 31 0, .addi 31 31 0,
        .lui 1 0, .addi 1 1 1,
        .slli 1 1 (BitVec.ofNat 64 32), .or 1 1 31] := by
  native_decide

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
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.const 1 0xffffffffffffffff) [] 0]⟩ =
      some [.ori 1 0 (BitVec.ofNat 64 0xfff)] := by
  native_decide

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
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longMul 4 5 6 7))) [] 0]⟩ =
      some [.mulHU 4 6 7, .mul 5 6 7] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.addCarry 4 5 6 7 8))) [] 0]⟩ =
      some [.sltu 31 0 8, .add 4 6 7, .sltu 5 4 7,
        .add 4 4 31, .sltu 31 4 31, .or 5 5 31] := by
  native_decide

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.get 4 .heapLength : StackProg (Word 64)) =
      some [
        .loadWordOffset 4 10 (0 - BitVec.ofNat 64 24)] := by
  native_decide

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.dataBufferWrite 7 6 : StackProg (Word 64)) =
      some [.storeWord 6 7] := by
  native_decide

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.codeBufferWrite 7 6 : StackProg (Word 64)) =
      some [.storeByte 6 7] := by
  native_decide

example :
    (compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.storeConsts 6 7 none : StackProg (Word 64))).isSome := by
  native_decide

example :
    compileWordProgramNatToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const 42) : WordProg Nat) =
      some [.ori 4 0 (BitVec.ofNat 64 42)] := by
  native_decide

example :
    compileWordProgramToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const (BitVec.ofNat 64 42)) : WordProg (Word 64)) =
      some [.ori 4 0 (BitVec.ofNat 64 42)] := by
  native_decide

example :
    compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } wordFfiRiscVConfig
      stackRemoveRiscVConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat) =
      some [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
        .addi 1 0 (BitVec.ofNat 64 24),
        .jal 0 (0 - BitVec.ofNat 64 68)] := by
  native_decide

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
  native_decide

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

end Flapjack.RiscV
