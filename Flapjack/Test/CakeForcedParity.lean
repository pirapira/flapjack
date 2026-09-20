import Flapjack.RiscV.CakeRegAlloc

/-! RISC-V `get_forced` traversal checks against the direct HOL oracle in
    `scripts/hol-probes/get_forced_probe.out`. -/

namespace Flapjack.Test.CakeForcedParity

open Flapjack
open Flapjack.RiscV.CakeRegAlloc

def addCarry : WordProg Nat :=
  .inst (.arith (.cakeAddCarry 1 3 4 5))

def longMul : WordProg Nat :=
  .inst (.arith (.longMul 1 2 3 4))

def nested : WordProg Nat :=
  .seq addCarry (.mustTerminate longMul)

/- Cake's `get_forced` drops self-edges while preserving each distinct
   carry edge (`reg_allocScript.sml`, `get_forced_def`). -/
def endpointDedup : WordProg Nat :=
  .seq
    (.inst (.arith (.cakeAddCarry 1 3 1 5)))
    (.inst (.arith (.cakeAddCarry 1 3 4 1)))

/- The original traversal visits a branch's then arm before its else arm and
   continues through loop bodies in the surrounding program order. -/
def branchLoop : WordProg Nat :=
  .seq
    (.ite .notEqual 2 (.reg 3) addCarry longMul)
    (.loop [] addCarry [])

def parityGuard : Bool :=
  cakeGetForced addCarry == [(1, 4), (1, 5)] &&
  cakeGetForced longMul == [(1, 3), (1, 4)] &&
  cakeGetForced nested == [(1, 4), (1, 5), (1, 3), (1, 4)] &&
  cakeGetForced endpointDedup == [(1, 5), (1, 4)] &&
  cakeGetForced branchLoop ==
    [(1, 4), (1, 5), (1, 3), (1, 4), (1, 4), (1, 5)]

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake get_forced HOL parity (including endpoint/traversal cases)"
  else
    IO.println "FAIL Cake get_forced HOL parity"
  pure parityGuard

end Flapjack.Test.CakeForcedParity
