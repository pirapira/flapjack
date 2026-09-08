import Flapjack.RiscV.CorrectnessCode

namespace Flapjack.Test.CorrectnessCode

open Flapjack Flapjack.RiscV

/- The branch selector is exercised for both a comparison and a bit test. -/
example [NeZero width] (offset : Word width) :
    riscVBranchFalseInstruction .equal 1 2 offset =
      .branchNe 1 2 offset := by
  rfl

example [NeZero width] (offset : Word width) :
    riscVBranchFalseInstruction .notTest 1 2 offset =
      .branchEq 1 2 offset := by
  rfl

example :
    (labCompileAsm ({ services := [] } : WordFfiContext)
      2 [(17, 23)] 4 (.locValue 4 ⟨2, 17⟩)).bind
        (fun code => executeInstructions (zeroState 64) code) =
      some (execute (zeroState 64)
        (.addi 4 0 (BitVec.ofNat 64 23))) := by
  apply labCompileAsm_locValue_execute
  · decide
  · decide

end Flapjack.Test.CorrectnessCode
