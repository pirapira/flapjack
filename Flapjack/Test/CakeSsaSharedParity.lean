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

def shareLoad8Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .load8 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .load8 9 (.var 0)) => true
  | _ => false

def shareStore8Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .store8 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .store8 0 (.var 0)) => true
  | _ => false

def shareLoad16Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .load16 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .load16 9 (.var 0)) => true
  | _ => false

def shareStore16Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .store16 7 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .store16 0 (.var 0)) => true
  | _ => false

def opCurrHeapGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.opCurrHeap .add 7 2 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.opCurrHeap .add 9 0) => true
  | _ => false

/- Cake reads the source through the entry SSA map before allocating the fresh
   destination for OpCurrHeap. -/
def mappedOpCurrHeapGuard : Bool :=
  match (wordFullSsaCcTrans 1
      (.opCurrHeap .add 0 0 : WordProg Nat)).2.2 with
  | .seq (.move 1 [(5, 0)]) (.opCurrHeap .add 9 5) => true
  | _ => false

def parityGuard : Bool :=
  shareLoadGuard && shareStoreGuard && shareLoad8Guard && shareStore8Guard &&
    shareLoad16Guard && shareStore16Guard && opCurrHeapGuard
    && mappedOpCurrHeapGuard

#guard shareLoadGuard
#guard shareStoreGuard
#guard shareLoad8Guard
#guard shareStore8Guard
#guard shareLoad16Guard
#guard shareStore16Guard
#guard opCurrHeapGuard
#guard mappedOpCurrHeapGuard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans ShareInst load freshens Cake destination", shareLoadGuard),
      ("ssa_cc_trans ShareInst store preserves Cake source", shareStoreGuard),
      ("ssa_cc_trans ShareInst load8 freshens Cake destination", shareLoad8Guard),
      ("ssa_cc_trans ShareInst store8 preserves Cake source", shareStore8Guard),
      ("ssa_cc_trans ShareInst load16 freshens Cake destination", shareLoad16Guard),
      ("ssa_cc_trans ShareInst store16 preserves Cake source", shareStore16Guard),
      ("ssa_cc_trans OpCurrHeap freshens Cake destination", opCurrHeapGuard),
      ("ssa_cc_trans OpCurrHeap reads the Cake entry SSA namespace",
        mappedOpCurrHeapGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaSharedParity
