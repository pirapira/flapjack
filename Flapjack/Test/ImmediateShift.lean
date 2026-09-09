import Flapjack.RiscV.CorrectnessImmediateShift

/-! Regression coverage for immediate shift Word lowering. -/

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.const amount))) =
      some (execute state (.slli 1 2 amount)) :=
  compileWordImmediateShiftLsl_sound state amount

example [NeZero width] (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.const amount))) =
      some (execute state (.srli 1 2 amount)) :=
  compileWordImmediateShiftLsr_sound state amount

example [NeZero width] (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.const amount))) =
      some (execute state (.srai 1 2 amount)) :=
  compileWordImmediateShiftAsr_sound state amount

end Flapjack.RiscV
