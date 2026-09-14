import Flapjack.LoopAnalysis

namespace Flapjack.Test.LoopMarkAllParity

/-! Direct parity for `loop_live$mark_all` (`loop_liveScript.sml:189`).
    The guards compare rebuilt children as well as the parent mark bit. -/
def parityGuard : Bool :=
  (match loopMarkAll
      (.seq (.skip) (.skip) : LoopProg Nat) with
  | (.mark (.seq (.mark .skip) (.mark .skip)), true) => true
  | _ => false) &&
  (match loopMarkAll
      (.seq (.loop [] .skip []) .skip : LoopProg Nat) with
  | (.seq (.loop [] (.mark .skip) []) (.mark .skip), false) => true
  | _ => false) &&
  (match loopMarkAll
      (.loop [] .skip [] : LoopProg Nat) with
  | (.loop [] (.mark .skip) [], false) => true
  | _ => false) &&
  (match loopMarkAll
      (.mark (.skip) : LoopProg Nat) with
  | (.mark .skip, true) => true
  | _ => false) &&
  (match loopMarkAll
      (.call none none [] none : LoopProg Nat) with
  | (.mark (.call none none [] none), true) => true
  | _ => false) &&
  (match loopMarkAll
      (.call (some ([1], [])) none [2]
        (some (3, .skip, .fail, [])) : LoopProg Nat) with
  | (.mark (.call (some ([1], [])) none [2]
      (some (3, .mark .skip, .mark .fail, []))), true) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.LoopMarkAllParity
