import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the remaining leaf/control rows of
    `ssa_cc_trans` in `word_allocScript.sml`.  The expected forms pin the
    recursive `MustTerminate` traversal, no-op `Tick`, fresh `LocValue`
    destination, and the no-loop-frame `Break`/`Continue` fallbacks. -/

namespace Flapjack.Test.CakeSsaLeafParity

open Flapjack

def mustTerminateGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.mustTerminate (.get 7 .heapLength) : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.mustTerminate (.get 9 .heapLength)) => true
  | _ => false

def tickGuard : Bool :=
  match (wordFullSsaCcTrans 0 (.tick : WordProg Nat)).2.2 with
  | .seq (.move 1 []) .tick => true
  | _ => false

def locValueGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.locValue 7 3 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.locValue 9 3) => true
  | _ => false

def breakGuard : Bool :=
  match (wordFullSsaCcTrans 0 (.break 0 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.break 0) => true
  | _ => false

def continueGuard : Bool :=
  match (wordFullSsaCcTrans 0 (.continue 0 : WordProg Nat)).2.2 with
  | .seq (.move 1 []) (.continue 0) => true
  | _ => false

def parityGuard : Bool :=
  mustTerminateGuard && tickGuard && locValueGuard && breakGuard && continueGuard

#guard mustTerminateGuard
#guard tickGuard
#guard locValueGuard
#guard breakGuard
#guard continueGuard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("ssa_cc_trans MustTerminate recurses like Cake", mustTerminateGuard),
      ("ssa_cc_trans Tick preserves Cake no-op", tickGuard),
      ("ssa_cc_trans LocValue freshens Cake destination", locValueGuard),
      ("ssa_cc_trans Break uses Cake no-frame fallback", breakGuard),
      ("ssa_cc_trans Continue uses Cake no-frame fallback", continueGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaLeafParity
