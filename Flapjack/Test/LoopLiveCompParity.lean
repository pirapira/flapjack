import Flapjack.Pancake.LoopLive

namespace Flapjack.Test.LoopLiveCompParity

/-! Direct parity for `loop_live$comp` (`loop_liveScript.sml:217`). -/
def parityGuard : Bool :=
  (match loopLiveComp (.skip : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveComp (.assign 1 (.const 7) : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveComp (.seq .skip .skip : LoopProg Nat) with
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false) &&
  (match loopLiveComp (.arith (.div 1 2 3) : LoopProg Nat) with
  | .mark (.arith (.div 1 2 3)) => true
  | _ => false) &&
  (match loopLiveComp (.return [7] : LoopProg Nat) with
  | .mark (.return [7]) => true
  | _ => false) &&
  (match loopLiveComp
      (.loop [1] (.assign 2 (.const 7)) [] : LoopProg Nat) with
  | .loop [1] (.mark .skip) [] => true
  | _ => false) &&
  (match loopLiveComp
      (.seq
        (.ite .notEqual 1 (.imm 0)
          (.assign 2 (.const 7)) (.assign 2 (.const 8)) [2])
        (.return [2]) : LoopProg Nat) with
  | .mark (.seq
      (.mark (.ite .notEqual 1 (.imm 0)
        (.mark (.assign 2 (.const 7)))
        (.mark (.assign 2 (.const 8))) [2]))
      (.mark (.return [2]))) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

def largeLiveInFuelMatchesCake : Bool :=
  loopFixedpointFuel (List.range 65) == 66

#guard largeLiveInFuelMatchesCake

end Flapjack.Test.LoopLiveCompParity
