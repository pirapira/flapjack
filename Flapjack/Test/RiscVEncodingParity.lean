import Flapjack.RiscV.Encoding

/-! Encoding parity with the CakeML RISC-V exporter (`export_riscvScript.sml`):
    the Word `Div` operation uses the signed DIV funct3/funct7 encoding. -/

namespace Flapjack.RiscV

example : encodeInstruction (width := 64) (.divU 1 2 3) =
    (0x023140B3 : BitVec 32) := by
  decide

example : encodeInstruction (width := 64) (.remU 1 2 3) =
    (0x023170B3 : BitVec 32) := by
  decide

end Flapjack.RiscV
