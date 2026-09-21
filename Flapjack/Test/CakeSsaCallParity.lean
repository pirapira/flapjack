import Flapjack.RiscV.Allocator

/-! Direct Cake parity for the returning `Call` equations in
    `cakeml/compiler/backend/word_allocScript.sml:494-535`.  These cases were
    intentionally kept separate from the return-free call guard: Cake refreshes
    the cut set and allocates a fresh return destination before emitting the call.
    The exact expected shape below was obtained from the canonical HOL probe
    `cake_call_probeScript.sml` using `full_ssa_cc_trans`. -/

namespace Flapjack.Test.CakeSsaCallParity

open Flapjack

def returningCallProgram : WordProg Nat :=
  .call (some ([4], ([], []), .return 4 [6], 9, 10)) (some 7) [0, 2] none

def returningCallGuard : Bool :=
  match (wordFullSsaCcTrans 2 returningCallProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2)])
      (.seq (.move 0 [])
        (.seq (.move 1 [(2, 9), (4, 13)])
          (.call (some ([2], ([], []),
            .seq (.move 0 [])
              (.seq (.move 1 [(21, 2)])
                (.seq (.move 0 [(2, 0)]) (.return 21 [2]))), 9, 10))
            (some 7) [2, 4] none))) => true
  | _ => false

#guard returningCallGuard

def returningCallCutsetProgram : WordProg Nat :=
  .call (some ([4], ([4], []), .return 4 [6], 9, 10)) (some 7) [0, 2] none

def returningCallCutsetGuard : Bool :=
  match (wordFullSsaCcTrans 2 returningCallCutsetProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2)])
      (.seq (.move 0 [(19, 0)])
        (.seq (.move 1 [(2, 9), (4, 13)])
          (.call (some ([2], ([19], []),
            .seq (.move 0 [(25, 19)])
              (.seq (.move 1 [(29, 2)])
                (.seq (.move 0 [(2, 0)]) (.return 29 [2]))), 9, 10))
            (some 7) [2, 4] none))) => true
  | _ => false

#guard returningCallCutsetGuard

def returningCallSkipProgram : WordProg Nat :=
  .call (some ([4], ([], []), .skip, 9, 10)) (some 7) [0, 2] none

def returningCallSkipGuard : Bool :=
  match (wordFullSsaCcTrans 2 returningCallSkipProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2)])
      (.seq (.move 0 [])
        (.seq (.move 1 [(2, 9), (4, 13)])
          (.call (some ([2], ([], []),
            (.seq (.move 0 []) (.seq (.move 1 [(21, 2)]) .skip)), 9, 10))
            (some 7) [2, 4] none))) => true
  | _ => false

#guard returningCallSkipGuard

def noReturnEmptyCallGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.call none (some 7) [] none : WordProg Nat)).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 []) (.call none (some 7) [] none)) => true
  | _ => false

#guard noReturnEmptyCallGuard

def noReturnEmptyHandlerCallGuard : Bool :=
  match (wordFullSsaCcTrans 0
      (.call none (some 7) [] (some (3, .skip, 11, 12)) : WordProg Nat)).2.2 with
  | .seq (.move 1 [])
      (.seq (.move 1 [])
        (.call none (some 7) [] (some (3, .skip, 11, 12)))) => true
  | _ => false

#guard noReturnEmptyHandlerCallGuard

def handlerCallProgram : WordProg Nat :=
  .call (some ([4], ([], []), .skip, 9, 10)) (some 7) [0, 2]
    (some (3, .skip, 11, 12))

def handlerCallGuard : Bool :=
  match (wordFullSsaCcTrans 2 handlerCallProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2)])
      (.seq (.move 0 [])
        (.seq (.move 1 [(2, 9), (4, 13)])
          (.call (some ([2], ([], []),
            .seq
              (.seq (.move 0 []) (.seq (.move 1 [(21, 2)]) .skip))
              (.seq (.move 1 [])
                (.seq (.seq .skip (.move 1 [(29, 21)]))
                  (.inst (.const 33 0)))), 9, 10))
            (some 7) [2, 4]
            (some (2,
              .seq
                (.seq (.move 0 []) (.seq (.move 1 [(25, 2)]) .skip))
                (.seq (.move 1 [])
                  (.seq (.seq .skip (.inst (.const 29 0)))
                    (.move 1 [(33, 25)]))),
              11, 12))))) => true
  | _ => false

#guard handlerCallGuard

def parityGuard : Bool :=
  returningCallGuard && returningCallCutsetGuard && returningCallSkipGuard &&
    noReturnEmptyCallGuard && noReturnEmptyHandlerCallGuard && handlerCallGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("full_ssa_cc_trans returning Call preserves Cake return ABI",
        returningCallGuard),
      ("full_ssa_cc_trans returning Call preserves Cake cut-set refresh",
        returningCallCutsetGuard),
      ("full_ssa_cc_trans returning Call preserves Cake skipped return handler",
        returningCallSkipGuard),
      ("full_ssa_cc_trans empty return-free Call preserves Cake Move1 []",
        noReturnEmptyCallGuard),
      ("full_ssa_cc_trans empty return-free handler Call preserves Cake Move1 []",
        noReturnEmptyHandlerCallGuard),
      ("full_ssa_cc_trans handler Call preserves Cake exception payload",
        handlerCallGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaCallParity
