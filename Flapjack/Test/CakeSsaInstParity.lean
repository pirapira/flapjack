import Flapjack.RiscV.Allocator

/-! Direct Cake parity for ordinary `ssa_cc_trans_inst` rows from
    `cakeml/compiler/backend/word_allocScript.sml:137-230`.  The exact shapes
    below come from the canonical HOL `full_ssa_cc_trans` probe
    `cake_inst_probeScript.sml`: ordinary arithmetic reads the SSA sources,
    while loads freshen the destination and stores preserve the source names. -/

namespace Flapjack.Test.CakeSsaInstParity

open Flapjack

def binOpRegisterProgram : WordProg Nat :=
  .inst (.arith (.binOp .add 1 2 (.reg 3)))

def binOpRegisterGuard : Bool :=
  match (wordFullSsaCcTrans 0 binOpRegisterProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.arith (.binOp .add 5 0 (.reg 0)))) => true
  | _ => false

#guard binOpRegisterGuard

def binOpImmediateProgram : WordProg Nat :=
  .inst (.arith (.binOp .add 1 2 (.imm 7)))

def binOpImmediateGuard : Bool :=
  match (wordFullSsaCcTrans 0 binOpImmediateProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.arith (.binOp .add 5 0 (.imm 7)))) => true
  | _ => false

#guard binOpImmediateGuard

def loadOffsetProgram : WordProg Nat :=
  .inst (.memOffset .load 1 2 4)

def loadOffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0 loadOffsetProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.memOffset .load 5 0 4)) => true
  | _ => false

#guard loadOffsetGuard

def storeOffsetProgram : WordProg Nat :=
  .inst (.memOffset .store 1 2 4)

def storeOffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0 storeOffsetProgram).2.2 with
  | .seq (.move 1 [])
      (.inst (.memOffset .store 0 0 4)) => true
  | _ => false

#guard storeOffsetGuard

def parityGuard : Bool :=
  binOpRegisterGuard && binOpImmediateGuard && loadOffsetGuard && storeOffsetGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans register Binop preserves Cake source mapping",
        binOpRegisterGuard),
      ("ssa_cc_trans immediate Binop preserves Cake immediate",
        binOpImmediateGuard),
      ("ssa_cc_trans Load preserves Cake offset and fresh destination",
        loadOffsetGuard),
      ("ssa_cc_trans Store preserves Cake offset and source mapping",
        storeOffsetGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaInstParity
