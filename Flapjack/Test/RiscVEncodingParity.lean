import Flapjack.RiscV.Encoding
import Flapjack.RiscV.ArtifactFormat

/-! Encoding and assembly-formatting parity with the CakeML RISC-V exporter
    (`export_riscvScript.sml`): signed DIV carries funct3 4 / funct7 1
    (`riscv_ast` Div), and bitmap data is emitted as split16 — sixteen
    `.quad` words per line, no line at all when empty. -/

namespace Flapjack.RiscV

example : encodeInstruction (width := 64) (.div 1 2 3) =
    (0x023140B3 : BitVec 32) := by
  decide

example : encodeInstruction (width := 64) (.divU 1 2 3) =
    (0x023150B3 : BitVec 32) := by
  decide

example : pancakeBitmapQuadLines [] = [] := by
  rfl

example : pancakeBitmapQuadLines (List.range 16) =
    ["\t.quad 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15"] := by
  decide

example : pancakeBitmapQuadLines (List.range 20) =
    ["\t.quad 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15",
     "\t.quad 16,17,18,19"] := by
  decide

end Flapjack.RiscV
