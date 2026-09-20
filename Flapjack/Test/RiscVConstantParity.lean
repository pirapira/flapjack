import Flapjack.RiscV.Backend

/-! Direct CakeML `riscv_ast (Inst (Const ...))` oracle checks.

`wordExpToInstruction` remains the theorem-facing one-instruction API.  These
checks cover the separate constants boundary, whose list shape follows
`riscv_targetScript.sml` (`riscv_ast_def` and `riscv_const32_def`). -/

namespace Flapjack.RiscV

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12) =
      some [.ori 4 0 (BitVec.ofNat 64 0x12)] := by
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

end Flapjack.RiscV
