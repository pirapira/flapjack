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

def parityGuard : Bool := setupTwoGuard && fullTransMoveGuard && limitBaseGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("setup_ssa numbers the parameters 5, 9 with next free name 13",
        setupTwoGuard),
      ("full_ssa_cc_trans prologue is the setup_ssa move", fullTransMoveGuard),
      ("limit_var supplies the fresh-name base", limitBaseGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaTempParity