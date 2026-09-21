import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the remaining memory-shaped `ssa_cc_trans` rows.
    The expected forms are the source equations in CakeML's
    `word_allocScript.sml`: `OpCurrHeap` renames its destination while reading
    the source, `ShareInst` loads freshen their destination, and stores retain
    the source read.  Address expressions are renamed before that distinction.
    These cases are separate from the ABI/control boundary guards because they
    feed the backend's shared-memory and current-heap instruction paths. -/

namespace Flapjack.Test.CakeSsaSharedParity

open Flapjack

def shareLoadGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .load 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .load 9 (.var 0)) => true
  | _ => false

def shareStoreGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .store 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .store 0 (.var 0)) => true
  | _ => false

def opCurrHeapGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.opCurrHeap .add 7 2 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.opCurrHeap .add 9 0) => true
  | _ => false

def parityGuard : Bool :=
  shareLoadGuard && shareStoreGuard && opCurrHeapGuard

#guard shareLoadGuard
#guard shareStoreGuard
#guard opCurrHeapGuard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans ShareInst load freshens Cake destination", shareLoadGuard),
      ("ssa_cc_trans ShareInst store preserves Cake source", shareStoreGuard),
      ("ssa_cc_trans OpCurrHeap freshens Cake destination", opCurrHeapGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaSharedParity
