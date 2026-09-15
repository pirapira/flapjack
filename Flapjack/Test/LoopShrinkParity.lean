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
  | _ => false) &&
  (match loopShrinkLeaf
      (.call none (some 7) [1, 2] none : LoopProg Nat) [2, 3] with
  | (.call none (some 7) [1, 2] none, [1, 2, 3]) => true
  | _ => false) &&
  (match loopShrinkLeaf
      (.call (some ([2], [1, 2, 3])) (some 7) [1] none : LoopProg Nat)
      [2, 3, 4] with
  | (.call (some ([2], [3])) (some 7) [1] none, [1, 3]) => true
  | _ => false) &&
  (match loopShrinkLeaf
      (.call (some ([2], [1, 2, 3])) (some 7) [1]
        (some (9, (.return [4] : LoopProg Nat), .skip, [2, 3])) :
          LoopProg Nat) [2, 3, 4] with
  | (.call (some ([2], [3])) (some 7) [1]
        (some (9, .return [4], .skip, [2, 3])), [1, 3]) => true
  | _ => false) &&
  -- Faithful `loop_live$fixedpoint` seeds the body with
  -- `bex = live_in ∪ (live_out ∩ l)` (loop_liveScript.sml:67-74,143-148),
  -- so the loop cut set keeps `live_in` (no HOL probe covered this case;
  -- the previous expectation recorded the old seed-`live_out`-only
  -- behaviour).
  (match loopShrinkLeaf
      (.loop [1] (.assign 2 (.const 7)) [] : LoopProg Nat) [] with
  | (.loop [1] .skip [], [1]) => true
  | _ => false) &&
  (match loopShrink [([5], [8])] (.continue 0 : LoopProg Nat) [] with
  | (.continue 0, [5]) => true
  | _ => false) &&
  (match loopShrink [([5], [8])] (.break 0 : LoopProg Nat) [] with
  | (.break 0, [8]) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopShrinkParity
