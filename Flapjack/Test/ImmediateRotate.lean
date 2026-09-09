import Flapjack.RiscV.CorrectnessImmediateRotate

/-! Regression coverage for immediate rotate-right Word lowering. -/

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .ror (.var 2) (.const amount))) =
      some (executeInstructions state
        [.srli 31 2 (shiftAmount amount),
         .slli 1 2 (BitVec.ofNat width ((width - shiftAmount amount) % width)),
         .or 1 1 31]) :=
  compileWordImmediateRotateRight_sound state amount

end Flapjack.RiscV
