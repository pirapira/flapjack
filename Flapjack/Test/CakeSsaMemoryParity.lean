import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the ordinary Word memory rows of `ssa_cc_trans`.
    These expected forms follow CakeML's `word_allocScript.sml`: Get freshens
    its destination, Store renames both its address expression and value source,
    and Set renames only its expression.  With no incoming SSA bindings,
    `option_lookup` intentionally supplies architectural zero. -/

namespace Flapjack.Test.CakeSsaMemoryParity

open Flapjack

def getGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.get 7 .heapLength : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.get 9 .heapLength) => true
  | _ => false

def storeGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.store (.var 2) 7 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.store (.var 0) 0) => true
  | _ => false

def setGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.set .heapLength (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.set .heapLength (.var 0)) => true
  | _ => false

def loadInstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .load 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .load 5 0)) => true
  | _ => false

def storeInstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .store 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .store 0 0)) => true
  | _ => false

def load32InstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .load32 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .load32 5 0)) => true
  | _ => false

def store32InstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .store32 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .store32 0 0)) => true
  | _ => false

def load8InstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .load8 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .load8 5 0)) => true
  | _ => false

def store8InstGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.mem .store8 1 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.mem .store8 0 0)) => true
  | _ => false

def loadOffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.memOffset .load 1 2 7) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.memOffset .load 5 0 7)) => true
  | _ => false

def storeOffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.memOffset .store 1 2 7) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.memOffset .store 0 0 7)) => true
  | _ => false

def load32OffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.memOffset .load32 1 2 7) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.memOffset .load32 5 0 7)) => true
  | _ => false

def store32OffsetGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.inst (.memOffset .store32 1 2 7) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.inst (.memOffset .store32 0 0 7)) => true
  | _ => false

/- Cake's shared-memory rows use the same `ssa_cc_trans_inst` carrier rule:
   a load freshens its destination, while a store reads both the source value
   and address through the current SSA map. -/
def shareLoadGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .load 1 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .load 5 (.var 0)) => true
  | _ => false

def shareStoreGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .store 1 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .store 0 (.var 0)) => true
  | _ => false

def shareLoad32Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .load32 1 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .load32 5 (.var 0)) => true
  | _ => false

def shareStore32Guard : Bool :=
  match (wordFullSsaCcTrans 0
      (.shareInst .store32 1 (.var 2) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.shareInst .store32 0 (.var 0)) => true
  | _ => false

def parityGuard : Bool :=
  getGuard && storeGuard && setGuard && loadInstGuard && storeInstGuard &&
    load32InstGuard && store32InstGuard && load8InstGuard && store8InstGuard &&
    loadOffsetGuard && storeOffsetGuard &&
    load32OffsetGuard && store32OffsetGuard && shareLoadGuard && shareStoreGuard &&
    shareLoad32Guard && shareStore32Guard

#guard getGuard
#guard storeGuard
#guard setGuard
#guard loadInstGuard
#guard load8InstGuard
#guard store8InstGuard
#guard storeInstGuard
#guard load32InstGuard
#guard store32InstGuard
#guard loadOffsetGuard
#guard storeOffsetGuard
#guard load32OffsetGuard
#guard store32OffsetGuard
#guard shareLoadGuard
#guard shareStoreGuard
#guard shareLoad32Guard
#guard shareStore32Guard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans Get freshens Cake destination", getGuard),
      ("ssa_cc_trans Store renames Cake address and value", storeGuard),
      ("ssa_cc_trans Set renames Cake expression only", setGuard),
      ("ssa_cc_trans Mem Load freshens Cake destination", loadInstGuard),
      ("ssa_cc_trans Mem Load8 freshens Cake destination", load8InstGuard),
      ("ssa_cc_trans Mem Store8 renames Cake address and value", store8InstGuard),
      ("ssa_cc_trans Mem Store renames Cake address and value", storeInstGuard),
      ("ssa_cc_trans Mem Load32 freshens Cake destination", load32InstGuard),
      ("ssa_cc_trans Mem Store32 renames Cake address and value", store32InstGuard),
      ("ssa_cc_trans MemOffset Load keeps Cake offset", loadOffsetGuard),
      ("ssa_cc_trans MemOffset Store keeps Cake offset", storeOffsetGuard),
      ("ssa_cc_trans MemOffset Load32 keeps Cake offset", load32OffsetGuard),
      ("ssa_cc_trans MemOffset Store32 keeps Cake offset", store32OffsetGuard),
      ("ssa_cc_trans shared Load freshens Cake destination", shareLoadGuard),
      ("ssa_cc_trans shared Store renames Cake address and value", shareStoreGuard),
      ("ssa_cc_trans shared Load32 freshens Cake destination", shareLoad32Guard),
      ("ssa_cc_trans shared Store32 renames Cake address and value", shareStore32Guard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaMemoryParity
