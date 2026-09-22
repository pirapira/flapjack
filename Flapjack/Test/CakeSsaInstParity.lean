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

/- These byte-memory rows are the exact `word_alloc_mem8_probe.out` results
   for Cake's `ssa_cc_trans_inst` equations at word_allocScript.sml:223-230. -/
def load8Program : WordProg Nat :=
  .inst (.mem .load8 1 2)

def load8Guard : Bool :=
  match (wordFullSsaCcTrans 0 load8Program).2.2 with
  | .seq (.move 1 [])
      (.inst (.mem .load8 5 0)) => true
  | _ => false

#guard load8Guard

def store8Program : WordProg Nat :=
  .inst (.mem .store8 1 2)

def store8Guard : Bool :=
  match (wordFullSsaCcTrans 0 store8Program).2.2 with
  | .seq (.move 1 [])
      (.inst (.mem .store8 0 0)) => true
  | _ => false

#guard store8Guard

def parityGuard : Bool :=
  binOpRegisterGuard && binOpImmediateGuard && loadOffsetGuard && storeOffsetGuard &&
    load8Guard && store8Guard

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
        storeOffsetGuard),
      ("ssa_cc_trans Load8 preserves Cake byte-load mapping",
        load8Guard),
      ("ssa_cc_trans Store8 preserves Cake byte-store mapping",
        store8Guard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaInstParity
