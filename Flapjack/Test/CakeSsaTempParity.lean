import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.CakeSsaTemp

/-! Direct HOL parity for CakeML `full_ssa_cc_trans` temporary numbering.
    Fixtures are in `scripts/hol-probes/cake_ssa_temp_probe.out`. -/

namespace Flapjack.Test.CakeSsaTempParity

open Flapjack
open Flapjack.RiscV.CakeAlloc
open Flapjack.RiscV.CakeRegAlloc

/-- The oracle's two-parameter examples both start free names at 5 and
number the parameters 5, 9 with the next free name 13. -/
def setupTwoGuard : Bool :=
  let result := cakeSetupSsa 2 5
      (.skip : WordProg Nat)
  (match result.1 with
   | .move priority moves => priority == 1 && moves == [(5, 0), (9, 2)]
   | _ => false) &&
    result.2.2 == 13

#guard setupTwoGuard

/-- The `full_ssa_cc_trans` prologue is exactly the `setup_ssa` move. -/
def isTwoMove (program : WordProg Nat) : Bool :=
  match program with
  | .move priority moves => priority == 1 && moves == [(5, 0), (9, 2)]
  | _ => false

def fullTransMoveGuard : Bool :=
  isTwoMove (cakeFullSsaCcTransMove 2 5
      (.skip : WordProg Nat)) &&
    isTwoMove (cakeSetupSsa 2 5 (.skip : WordProg Nat)).1

#guard fullTransMoveGuard

/-- `limit_var` supplies the fresh-name base the prologue numbers from. -/
def limitBaseGuard : Bool :=
  limitVar 0 == 5 && limitVar 26 == 29

#guard limitBaseGuard

/-- The oracle's `limit_two_assigns` case: the two-assign program has
`max_var` 2, so `limit_var` is 2 + (4 - 2) + 1 = 5. -/
def limitTwoAssignsGuard : Bool :=
  limitVar 2 == 5

#guard limitTwoAssignsGuard

/-- The two-assign program used by the `setup_two_next`/`full_two_assigns`
oracle cases. -/
def twoAssigns : WordProg Nat :=
  .seq (.assign 0 (.const 0)) (.assign 2 (.var 0))

/-- The oracle's `setup_two_next` case: `setup_ssa` at `limit_var` of the
two-assign program reaches the same prologue and next free name 13. -/
def setupTwoNextGuard : Bool :=
  isTwoMove (cakeSetupSsa 2 5 twoAssigns).1 &&
    (cakeSetupSsa 2 5 twoAssigns).2.2 == 13

#guard setupTwoNextGuard

/-- The oracle's `full_skip` case: `full_ssa_cc_trans` on `Skip` has the same
`setup_ssa` prologue, as does the two-assign program. -/
def fullSkipMoveGuard : Bool :=
  isTwoMove (cakeFullSsaCcTransMove 2 5 (.skip : WordProg Nat)) &&
    isTwoMove (cakeFullSsaCcTransMove 2 5 twoAssigns)

#guard fullSkipMoveGuard

/-! The checked source-shaped `wordFullSsaCcTrans` boundary must preserve the
    full Cake result, not only its entry move.  This is the `full_two_assigns`
    oracle from `cake_ssa_temp_probe.out`: after the parameter prologue, the
    two source assignments receive fresh names 13 and 17, and the second read
    observes the first fresh name. -/
def fullTwoAssignsGuard : Bool :=
  match (wordFullSsaCcTrans 2 twoAssigns).2.2 with
  | .seq (.move priority moves)
      (.seq (.assign 13 (.const 0)) (.assign 17 (.var 13))) =>
      priority == 1 && moves == [(5, 0), (9, 2)]
  | _ => false

#guard fullTwoAssignsGuard

/-! Branch and loop cases from the canonical Cake `ssa_cc_trans` equations
    (`word_allocScript.sml:391-590`).  These pin the branch continuation
    reconciliation and loop-entry/back-edge moves that feed IRC frame
    allocation.  The expected shapes were obtained with the canonical HOL
    `full_ssa_cc_trans` oracle. -/
def branchProgram : WordProg Nat :=
  .ite .equal 0 (.reg 2)
    (.seq (.assign 0 (.const 1)) (.assign 2 (.var 0)))
    (.assign 2 (.const 2))

def branchSsaGuard : Bool :=
  match (wordFullSsaCcTrans 2 branchProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.ite .equal 5 (.reg 9)
        (.seq
          (.seq (.assign 13 (.const 1)) (.assign 17 (.var 13)))
          (.seq (.move 1 [(29, 13), (25, 17)]) .skip))
        (.seq (.assign 21 (.const 2))
          (.seq (.move 1 [(29, 5), (25, 21)]) .skip))) => true
  | _ => false

def branchSkipProgram : WordProg Nat :=
  .ite .equal 0 (.reg 2) .skip (.assign 2 (.const 2))

def branchSkipSsaGuard : Bool :=
  match (wordFullSsaCcTrans 2 branchSkipProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.ite .equal 5 (.reg 9)
        (.seq .skip (.seq (.move 2 [(17, 9)]) .skip))
        (.seq (.assign 13 (.const 2))
          (.seq (.move 1 [(17, 13)]) .skip))) => true
  | _ => false

def loopProgram : WordProg Nat :=
  .loop [0] (.seq (.assign 0 (.const 1)) (.continue 0)) []

def loopSsaGuard : Bool :=
  match (wordFullSsaCcTrans 2 loopProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.seq .skip (.move 0 [(13, 5)]))
        (.loop [13]
          (.seq
            (.seq (.assign 17 (.const 1))
              (.seq (.move 1 [(13, 17)]) (.continue 0)))
            (.move 1 [(13, 17)])) [])) => true
  | _ => false

def loopLiveOutProgram : WordProg Nat :=
  .loop [0, 2] (.seq (.assign 0 (.const 1)) (.continue 0)) [2]

def loopLiveOutGuard : Bool :=
  match (wordFullSsaCcTrans 2 loopLiveOutProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.seq .skip (.move 0 [(13, 5), (17, 9)]))
        (.loop [17, 13]
          (.seq
            (.seq (.assign 21 (.const 1))
              (.seq (.move 1 [(13, 21)]) (.continue 0)))
            (.move 1 [(13, 21)])) [17])) => true
  | _ => false

def loopBreakProgram : WordProg Nat :=
  .loop [0] (.seq (.assign 0 (.const 1)) (.break 0)) []

def loopBreakGuard : Bool :=
  match (wordFullSsaCcTrans 2 loopBreakProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.seq .skip (.move 0 [(13, 5)]))
        (.loop [13]
          (.seq
            (.seq (.assign 17 (.const 1)) (.break 0))
            (.move 1 [(13, 17)])) [])) => true
  | _ => false

/-! Cake's break reconciliation also preserves a live value outside the loop;
    this is the live-out companion to `loopBreakGuard`. -/
def loopBreakLiveOutProgram : WordProg Nat :=
  .loop [0, 2] (.seq (.assign 0 (.const 1)) (.break 0)) [2]

def loopBreakLiveOutGuard : Bool :=
  match (wordFullSsaCcTrans 2 loopBreakLiveOutProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.seq .skip (.move 0 [(13, 5), (17, 9)]))
        (.loop [17, 13]
          (.seq
            (.seq (.assign 21 (.const 1)) (.break 0))
            (.move 1 [(13, 21)])) [17])) => true
  | _ => false

#guard branchSsaGuard
#guard branchSkipSsaGuard
#guard loopSsaGuard
#guard loopLiveOutGuard
#guard loopBreakGuard
#guard loopBreakLiveOutGuard

def parityGuard : Bool :=
  setupTwoGuard && fullTransMoveGuard && limitBaseGuard &&
    limitTwoAssignsGuard && setupTwoNextGuard && fullSkipMoveGuard &&
    fullTwoAssignsGuard && branchSsaGuard && branchSkipSsaGuard &&
    loopSsaGuard && loopLiveOutGuard && loopBreakGuard && loopBreakLiveOutGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("setup_ssa numbers the parameters 5, 9 with next free name 13",
        setupTwoGuard),
      ("full_ssa_cc_trans prologue is the setup_ssa move", fullTransMoveGuard),
      ("limit_var supplies the fresh-name base", limitBaseGuard),
      ("limit_var on the two-assign program is 5", limitTwoAssignsGuard),
      ("setup_ssa at the two-assign limit matches the oracle", setupTwoNextGuard),
      ("full_ssa_cc_trans on Skip and two assigns share the setup prologue",
        fullSkipMoveGuard),
      ("full_ssa_cc_trans preserves the Cake two-assignment body",
        fullTwoAssignsGuard),
      ("full_ssa_cc_trans reconciles Cake branch continuations",
        branchSsaGuard),
      ("full_ssa_cc_trans preserves Cake skipped branch sequences",
        branchSkipSsaGuard),
      ("full_ssa_cc_trans reconciles Cake loop back edges", loopSsaGuard),
      ("full_ssa_cc_trans preserves Cake loop exit cut sets",
        loopLiveOutGuard),
      ("full_ssa_cc_trans preserves Cake loop break reconciliation",
        loopBreakGuard),
      ("full_ssa_cc_trans preserves Cake live-out break reconciliation",
        loopBreakLiveOutGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaTempParity
