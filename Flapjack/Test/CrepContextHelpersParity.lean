import Flapjack.CrepToLoop

/-! Direct parity for `gen_temps`, `rt_var`, and `rt_vars`
(`crep_to_loopScript.sml:101-118`). -/
namespace Flapjack.Test.CrepContextHelpersParity

def context : NatInfoMap Nat := [(1, 5), (2, 6)]

def parityGuard : Bool :=
  crepGenTemps 7 3 == [7, 8, 9] &&
  crepRtVar context none 9 10 == 9 &&
  crepRtVar context (some 1) 9 10 == 5 &&
  crepRtVar context (some 3) 9 10 == 11 &&
  crepRtVars context [1, 2] 10 == [5, 6] &&
  crepRtVars [(1, 5)] [1, 2] 10 == [11]

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepContextHelpersParity
