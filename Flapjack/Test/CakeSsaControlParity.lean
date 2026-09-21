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

def longMulProgram : WordProg Nat :=
  .inst (.arith (.longMul 1 2 3 4))

/-! The neighboring Cake LongMul row uses the same fixed operand carriers,
    with the two fresh results copied back in destination-right/left order. -/
def longMulBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 longMulProgram).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 [(0, 0), (4, 0)])
        (.seq (.inst (.arith (.longMul 6 0 0 4)))
          (.move 1 [(13, 0), (9, 6)]))) => true
  | _ => false

#guard longMulBoundaryGuard

def shiftProgram : WordProg Nat :=
  .inst (.arith (.shift .lsl 1 2 (.reg 3)))

/-! A register-valued Cake shift uses fixed register 8 for the shift amount;
    the source move is part of `ssa_cc_trans_inst`, not a later backend pass. -/
def shiftBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 shiftProgram).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 [(8, 0)])
        (.inst (.arith (.shift .lsl 5 0 (.reg 8))))) => true
  | _ => false

#guard shiftBoundaryGuard

def addCarryProgram : WordProg Nat :=
  .inst (.arith (.cakeAddCarry 1 2 3 4))

/-! Cake's four-register AddCarry fixes the carry input/output at register 0;
    the fresh result and carry names are restored by the surrounding moves. -/
def addCarryBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 addCarryProgram).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 [(0, 0)])
        (.seq (.inst (.arith (.cakeAddCarry 9 0 0 0)))
          (.move 1 [(13, 0)]))) => true
  | _ => false

#guard addCarryBoundaryGuard

def constProgram : WordProg Nat :=
  .inst (.const 1 7)

def constBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 constProgram).2.2 with
  | .seq (.move 1 []) (.inst (.const 5 7)) => true
  | _ => false

#guard constBoundaryGuard

def binOpProgram : WordProg Nat :=
  .inst (.arith (.binOp .add 1 2 (.reg 3)))

def binOpBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 binOpProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.arith (.binOp .add 5 0 (.reg 0)))) => true
  | _ => false

#guard binOpBoundaryGuard

def divProgram : WordProg Nat :=
  .inst (.arith (.div 1 2 3))

def divBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 0 divProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.arith (.div 5 0 0))) => true
  | _ => false

#guard divBoundaryGuard

def parityGuard : Bool :=
  raiseBoundaryGuard && callBoundaryGuard && storeConstsBoundaryGuard &&
    longDivBoundaryGuard && longMulBoundaryGuard && shiftBoundaryGuard &&
    addCarryBoundaryGuard && constBoundaryGuard && binOpBoundaryGuard &&
    divBoundaryGuard

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
        longDivBoundaryGuard),
      ("full_ssa_cc_trans LongMul preserves Cake fixed-register ABI",
        longMulBoundaryGuard),
      ("full_ssa_cc_trans register Shift preserves Cake fixed-register ABI",
        shiftBoundaryGuard),
      ("full_ssa_cc_trans AddCarry preserves Cake fixed-register ABI",
        addCarryBoundaryGuard),
      ("full_ssa_cc_trans Const freshens Cake destination",
        constBoundaryGuard),
      ("full_ssa_cc_trans Binop rewrites Cake register operands",
        binOpBoundaryGuard),
      ("full_ssa_cc_trans Div rewrites Cake operands",
        divBoundaryGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaControlParity
