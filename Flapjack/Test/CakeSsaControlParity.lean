import Flapjack.RiscV.Allocator

/-! Direct HOL parity for the Raise, return-free Call, and StoreConsts rows of
    CakeML's `full_ssa_cc_trans` (`word_allocScript.sml:347-590`).  The exact
    shapes below were regenerated from canonical HOL with a temporary probe
    run from the Cake backend; the temporary source is intentionally not
    checked into the repository. -/

namespace Flapjack.Test.CakeSsaControlParity

open Flapjack

def raiseProgram : WordProg Nat :=
  .raise 2

def raiseBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 2 raiseProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.move 1 [(2, 9)]) (.raise 2)) => true
  | _ => false

#guard raiseBoundaryGuard

def callProgram : WordProg Nat :=
  .call none (some 7) [0, 2] none

def callBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 2 callProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.move 1 [(0, 5), (2, 9)])
        (.call none (some 7) [0, 2] none)) => true
  | _ => false

#guard callBoundaryGuard

def storeConstsProgram : WordProg Nat :=
  .storeConsts 1 2 3 4 []

def storeConstsBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 2 storeConstsProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2)])
      (.seq (.move 1 [(4, 0), (6, 0)])
        (.seq (.storeConsts 0 2 4 6 [])
          (.move 1 [(21, 4), (17, 6)]))) => true
  | _ => false

#guard storeConstsBoundaryGuard

def longDivProgram : WordProg Nat :=
  .inst (.arith (.longDiv 1 2 3 4 5))

/-! Cake's `ssa_cc_trans_inst` routes LongDiv through the fixed operand
    registers, then copies the quotient/remainder results into fresh SSA
    names.  This is the source-level contract used before the RISC-V target's
    software helper selection. -/
def longDivBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 longDivProgram).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 [(6, 0), (0, 0)])
        (.seq (.inst (.arith (.longDiv 0 6 6 0 0)))
          (.move 1 [(9, 6), (13, 0)]))) => true
  | _ => false

#guard longDivBoundaryGuard

def parityGuard : Bool :=
  raiseBoundaryGuard && callBoundaryGuard && storeConstsBoundaryGuard &&
    longDivBoundaryGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("full_ssa_cc_trans Raise preserves Cake exception ABI move",
        raiseBoundaryGuard),
      ("full_ssa_cc_trans return-free Call preserves Cake argument ABI",
        callBoundaryGuard),
      ("full_ssa_cc_trans StoreConsts preserves Cake reload moves",
        storeConstsBoundaryGuard),
      ("full_ssa_cc_trans LongDiv preserves Cake fixed-register ABI",
        longDivBoundaryGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaControlParity
