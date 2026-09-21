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

def parityGuard : Bool :=
  getGuard && storeGuard && setGuard && loadInstGuard && storeInstGuard &&
    load32InstGuard && store32InstGuard

#guard getGuard
#guard storeGuard
#guard setGuard
#guard loadInstGuard
#guard storeInstGuard
#guard load32InstGuard
#guard store32InstGuard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans Get freshens Cake destination", getGuard),
      ("ssa_cc_trans Store renames Cake address and value", storeGuard),
      ("ssa_cc_trans Set renames Cake expression only", setGuard),
      ("ssa_cc_trans Mem Load freshens Cake destination", loadInstGuard),
      ("ssa_cc_trans Mem Store renames Cake address and value", storeInstGuard),
      ("ssa_cc_trans Mem Load32 freshens Cake destination", load32InstGuard),
      ("ssa_cc_trans Mem Store32 renames Cake address and value", store32InstGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaMemoryParity
