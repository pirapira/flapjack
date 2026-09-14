import Flapjack.LoopAnalysis

/-! Direct parity for `loop_live$vars_of_exp_def` at
`cakeml/pancake/loop_liveScript.sml:11`.  The expected lists are the printed
HOL `num_set` results from `vars_of_exp_probe.out`. -/
namespace Flapjack.Test.LoopVarsOfExpParity

def parityGuard : Bool :=
  varsOfExp (.var 3 : LoopExp Nat) [] == [3] &&
  varsOfExp (.const 7 : LoopExp Nat) [9] == [9] &&
  varsOfExp (.load (.var 4) : LoopExp Nat) [9] == [4, 9] &&
  varsOfExp
      (.op .add [.var 3, .const 1, .var 2] : LoopExp Nat) [] == [2, 3] &&
  varsOfExp
      (.shift .lsl (.var 6) (.load (.var 1)) : LoopExp Nat) [8] == [1, 6, 8]

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopVarsOfExpParity
