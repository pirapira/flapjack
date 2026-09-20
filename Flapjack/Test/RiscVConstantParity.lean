import Flapjack.RiscV.Backend
import Flapjack.RiscV.Encoding

/-! Direct CakeML `riscv_ast (Inst (Const ...))` oracle checks.

`wordExpToInstruction` remains the theorem-facing one-instruction API.  These
checks cover the separate constants boundary, whose list shape follows
`riscv_targetScript.sml` (`riscv_ast_def` and `riscv_const32_def`). -/

namespace Flapjack.RiscV

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12) =
      some [.ori 4 0 (BitVec.ofNat 64 0x12)] := by
  decide

/-! Signed-12 endpoints from Cake's `valid_imm`/`riscv_ast` boundary. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2047) =
      some [.ori 4 0 (BitVec.ofNat 64 0x7ff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 2048)) =
      some [.ori 4 0 (BitVec.ofNat 64 0x800)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12345678) =
      some [.lui 4 (BitVec.ofNat 64 0x12345),
        .addi 4 4 (BitVec.ofNat 64 0x678)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) =
      some [.lui 31 (BitVec.ofNat 64 0x55667),
        .addi 31 31 (BitVec.ofNat 64 0x788),
        .lui 4 (BitVec.ofNat 64 0x11223),
        .addi 4 4 (BitVec.ofNat 64 0x344),
        .slli 4 4 (BitVec.ofNat 64 32),
        .or 4 4 31] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 (2 ^ 64 - 8)) =
      some [.ori 4 0 (BitVec.ofNat 64 0xff8)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2048) =
      some [.lui 4 (BitVec.ofNat 64 0xfffff),
        .xori 4 4 (BitVec.ofNat 64 0x800)] := by
  decide

/- The checked expression boundary routes constants through the Cake list
   lowering while preserving the old selector for all other expressions. -/
example :
    wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1234)) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  decide

example :
    wordExpToInstructionsCake (width := 64) 4
        (.load (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234),
        .loadWord 4 31] := by
  decide

example :
    wordProgToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordProgToRiscVCake (width := 64)
        (.inst (.const 4 (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordInstToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVCake (width := 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVCake,
    wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

def cakeConstFunctionExecution : Option (List (Word 64)) :=
  (wordFunctionToRiscVCake (width := 64)
    (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
      (.return 0 [4]))).map fun (code, returns) =>
    returns.map (readRegister (executeInstructions (zeroState 64) code))

#guard cakeConstFunctionExecution = some [BitVec.ofNat 64 0x1234]

/-! Executable obligations for the Cake-faithful multi-instruction boundary.

These deliberately exercise the emitted instruction list, rather than the
legacy one-instruction expression API. -/
theorem cakeConst1234_execution_oracle :
    (wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1234) := by
  decide

theorem cakeConstWide_execution_oracle :
    (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1122334455667788) := by
  decide

/-! `wordExpToInstruction` is not Cake-faithful for constants outside the
signed 12-bit immediate range: it returns a single `addi` whose immediate the
encoder silently truncates, while `wordConstToInstructions` emits the
`lui`/`addi` (or wider) sequence of `riscv_targetScript.sml:96`.  The witness
below records the information loss so callers that need the Cake shape use the
`wordConstToInstructions` boundary. -/

example :
    wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234)) =
      some (.addi 4 0 (BitVec.ofNat 64 0x1234)) := by
  decide

example :
    encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x1234)) =
      encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234)) := by
  decide

example :
    (wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234))).map
        (fun instruction => encodeInstruction instruction) =
      some (encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234))) := by
  decide

end Flapjack.RiscV
