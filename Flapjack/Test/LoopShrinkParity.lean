import Flapjack.LoopAnalysis

namespace Flapjack.Test.LoopShrinkParity

/-! Executable leaf equations corresponding to the direct `loop_live$shrink`
    observations in `scripts/hol-probes/shrink_leaf_probe.out`. -/
def parityGuard : Bool :=
  (match loopShrinkLeaf (.skip : LoopProg Nat) [1, 2] with
  | (.skip, [1, 2]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.assign 1 (.const 7) : LoopProg Nat) [1, 2] with
  | (.assign 1 (.const 7), [2]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.assign 1 (.const 7) : LoopProg Nat) [2] with
  | (.skip, [2]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.assign 1 (.var 3) : LoopProg Nat) [1, 2] with
  | (.assign 1 (.var 3), [2, 3]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.arith (.div 1 2 3) : LoopProg Nat) [1, 2] with
  | (.arith (.div 1 2 3), [2, 3]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.store (.var 4 : LoopExp Nat) 5) [] with
  | (.store (.var 4) 5, [4, 5]) => true
  | _ => false) &&
  (match loopShrinkLeaf (.load32 1 2 : LoopProg Nat) [] with
  | (.load32 1 2, [1]) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopShrinkParity
