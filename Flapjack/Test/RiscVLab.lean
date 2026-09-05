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

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .add 4 5 6) [] 0]⟩ =
      some [.add 4 5 6] := by
  native_decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shift .lsl 4 5 6) [] 0]⟩ =
      some [.sll 4 5 6] := by
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

end Flapjack.RiscV
