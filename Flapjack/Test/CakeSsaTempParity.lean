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

def parityGuard : Bool :=
  setupTwoGuard && fullTransMoveGuard && limitBaseGuard &&
    limitTwoAssignsGuard && setupTwoNextGuard && fullSkipMoveGuard

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
        fullSkipMoveGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaTempParity