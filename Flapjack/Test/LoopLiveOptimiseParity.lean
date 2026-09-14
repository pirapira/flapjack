import Flapjack.LoopAnalysis

namespace Flapjack.Test.LoopLiveOptimiseParity

/-! Direct parity for `loop_live$optimise` (`loop_liveScript.sml:221`). -/
def parityGuard : Bool :=
  (match loopLiveOptimise (.skip : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveOptimise (.locValue 3 7 : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveOptimise (.seq .skip .skip : LoopProg Nat) with
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false) &&
  (match loopLiveOptimise (.ffi "f" 1 2 3 4 [] : LoopProg Nat) with
  | .mark (.ffi "f" 1 2 3 4 []) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopLiveOptimiseParity
