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

def parityGuard : Bool :=
  cakeGetForced addCarry == [(1, 3), (1, 4)] &&
  cakeGetForced longMul == [(1, 3), (1, 4)] &&
  cakeGetForced nested == [(1, 3), (1, 4), (1, 3), (1, 4)]

#guard parityGuard
#eval parityGuard

end Flapjack.Test.CakeForcedParity
