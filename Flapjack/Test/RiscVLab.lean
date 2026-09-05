import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

example :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.addi 14 0 (BitVec.ofNat 64 7), .ecall] := by
  native_decide

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
        .addi 1 0 (BitVec.ofNat 64 7)] := by
  native_decide

end Flapjack.RiscV
