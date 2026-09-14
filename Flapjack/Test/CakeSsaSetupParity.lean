import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.CakeSsaSetup

/-! Direct HOL parity for CakeML `total_colour` and `setup_ssa`.
    Fixtures are in `scripts/hol-probes/word_alloc_setup_colour_probe.out`. -/

namespace Flapjack.Test.CakeSsaSetupParity

open Flapjack
open Flapjack.RiscV.CakeAlloc
open Flapjack.RiscV.CakeRegAlloc

def totalColourGuard : Bool :=
  totalColour [(1, 7), (3, 9)] 1 == 14 &&
    totalColour [(1, 7), (3, 9)] 3 == 18 &&
    totalColour [(1, 7), (3, 9)] 2 == 2 &&
    totalColour [(1, 7), (3, 9)] 5 == 0

#guard totalColourGuard

def isEntryMove (program : WordProg Nat) : Bool :=
  match program with
  | .move priority moves => priority == 1 && moves == [(5, 0), (9, 2), (13, 4)]
  | _ => false

def setupSsaGuard : Bool :=
  let result := cakeSetupSsa 3 5
      (.skip : WordProg Nat)
  isEntryMove result.1 &&
    result.2.1.next == 17 &&
    lookupNatInfo 0 result.2.1.current == some 5 &&
    lookupNatInfo 2 result.2.1.current == some 9 &&
    lookupNatInfo 4 result.2.1.current == some 13 &&
    result.2.2 == 17

#guard setupSsaGuard

def setupSsaEmptyGuard : Bool :=
  let result := cakeSetupSsa 0 9
      (.skip : WordProg Nat)
  (match result.1 with
   | .move priority moves => priority == 1 && moves == []
   | _ => false) &&
    result.2.1.next == 9 && result.2.2 == 9

#guard setupSsaEmptyGuard

def parityGuard : Bool := totalColourGuard && setupSsaGuard && setupSsaEmptyGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake setup_ssa/total_colour HOL parity"
  else
    IO.println "FAIL Cake setup_ssa/total_colour HOL parity"
  pure parityGuard

end Flapjack.Test.CakeSsaSetupParity
