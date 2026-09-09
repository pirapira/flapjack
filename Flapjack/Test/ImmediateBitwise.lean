import Flapjack.RiscV.CorrectnessImmediateBitwise

/-! Regression coverage for immediate bitwise Word lowering. -/

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .and [.var 2, .const value])) =
      some (execute state (.andi 1 2 value)) :=
  compileWordImmediateAnd_sound state value

example [NeZero width] (state : State width) (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .or [.var 2, .const value])) =
      some (execute state (.ori 1 2 value)) :=
  compileWordImmediateOr_sound state value

example [NeZero width] (state : State width) (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .xor [.var 2, .const value])) =
      some (execute state (.xori 1 2 value)) :=
  compileWordImmediateXor_sound state value

end Flapjack.RiscV
