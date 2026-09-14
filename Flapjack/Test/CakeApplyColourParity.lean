import Flapjack.RiscV.OracleAllocator

/-! Direct HOL parity for CakeML `total_colour` followed by `apply_colour`.
    The source fixture is `scripts/hol-probes/apply_colour_probe.out`. -/

namespace Flapjack.Test.CakeApplyColourParity

open Flapjack

def oracle : NatInfoMap Nat := [(1, 7), (3, 9)]

def totalColourExact : Bool :=
  wordOracleColour oracle 1 == 14 &&
    wordOracleColour oracle 2 == 2 &&
    wordOracleColour oracle 7 == 0

#guard totalColourExact

def assignExact : Bool :=
  match wordApplyTotalColour oracle
      (.assign 1 (.var 3) : WordProg Nat) with
  | .assign name (.var source) => name == 14 && source == 18
  | _ => false

#guard assignExact

def returnRaiseExact : Bool :=
  match wordApplyTotalColour oracle
      (.seq (.return 1 [3, 5]) (.raise 7) : WordProg Nat) with
  | .seq (.return label values) (.raise exception) =>
      label == 14 && values == [18, 0] && exception == 0
  | _ => false

#guard returnRaiseExact

def callHandlerExact : Bool :=
  match wordApplyTotalColour oracle
      (.call
        (some ([1], ([3], [5]), .return 1 [3], 10, 11))
        (some 12) [1, 3]
        (some (7, .raise 3, 13, 14)) : WordProg Nat) with
  | .call (some (values, (normal, exception), .return label returned,
      returnLabel, entryLabel)) (some target) arguments
      (some (handlerException, .raise raised, handlerLabel, handlerEntry)) =>
      values == [14] && normal == [18] && exception == [0] &&
        label == 14 && returned == [18] && returnLabel == 10 &&
        entryLabel == 11 && target == 12 && arguments == [14, 18] &&
        handlerException == 0 && raised == 18 && handlerLabel == 13 &&
        handlerEntry == 14
  | _ => false

#guard callHandlerExact

def loopLiveExact : Bool :=
  match wordApplyTotalColour oracle
      (.loop [1, 7] (.assign 1 (.var 3)) [3] : WordProg Nat) with
  | .loop liveIn (.assign name (.var source)) liveOut =>
      liveIn == [0, 14] && name == 14 && source == 18 && liveOut == [18]
  | _ => false

#guard loopLiveExact

def parityGuard : Bool :=
  totalColourExact && assignExact && returnRaiseExact &&
    callHandlerExact && loopLiveExact

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake apply_colour/total_colour HOL parity"
  else
    IO.println "FAIL Cake apply_colour/total_colour HOL parity"
  pure parityGuard

end Flapjack.Test.CakeApplyColourParity
