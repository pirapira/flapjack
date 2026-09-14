import Flapjack.LoopAnalysis

/-! Direct parity for `loop_live$arith_vars_def` at
`cakeml/pancake/loop_liveScript.sml:50`. -/
namespace Flapjack.Test.LoopArithVarsParity

def parityGuard : Bool :=
  arithVars (.longMul 1 2 3 4) [1, 2, 6] == [3, 4, 6] &&
  arithVars (.div 1 2 3) [1, 5] == [2, 3, 5] &&
  arithVars (.longDiv 1 2 3 4 5) [1, 2, 8] == [3, 4, 5, 8]

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopArithVarsParity
