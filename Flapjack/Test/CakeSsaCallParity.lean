import Flapjack.RiscV.Allocator
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordDeadCode

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

def productionNoReturnEmptyCallGuard : Bool :=
  match Flapjack.RiscV.CakeRegAlloc.cakeAllocateWordFunction
      ([] : List Nat)
      (.call none (some 7) [] none : WordProg Nat) 0 3 with
  | some (_, _,
      .seq (.move 1 [])
        (.seq (.move 1 []) (.call none (some 7) [] none)), _) => true
  | _ => false

#guard productionNoReturnEmptyCallGuard

def productionAfterDeadNoReturnEmptyCallGuard : Bool :=
  match Flapjack.RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
      0 ([] : List Nat) (.call none (some 7) [] none : WordProg Nat) with
  | some (_, _, .call none (some 7) [] none, _) => true
  | _ => false

#guard productionAfterDeadNoReturnEmptyCallGuard

def handlerCallProgram : WordProg Nat :=
  .call (some ([4], ([], []), .skip, 9, 10)) (some 7) [0, 2]
    (some (3, .skip, 11, 12))

def returningHandlerProgram : WordProg Nat :=
  .call (some ([4, 6], ([], []), .return 4 [6, 8], 9, 10)) (some 7) [0, 2]
    (some (3, .raise 5, 11, 12))

/- Cake's returning Call with an exception handler refreshes both continuations:
   the return path preserves both result carriers, while the exception path
   moves the payload into ABI register 2 before Raise. -/
def returningHandlerReturnShape : WordProg Nat → Bool
  | .seq
      (.seq (.move 0 [])
        (.seq (.move 1 [(25, 2), (29, 4)])
          (.seq (.move 0 [(2, 29), (4, 0)])
            (.return 25 [2, 4]))))
      (.seq (.move 1 [])
        (.seq
          (.seq (.seq .skip (.move 1 [(37, 29)]))
            (.move 1 [(41, 25)]))
          (.inst (.const 45 0)))) => true
  | _ => false

def returningHandlerExceptionShape : WordProg Nat → Bool
  | .seq
      (.seq (.move 0 [])
        (.seq (.move 1 [(33, 2)])
          (.seq (.move 1 [(2, 0)]) (.raise 2))))
      (.seq (.move 1 [])
        (.seq
          (.seq (.seq .skip (.inst (.const 37 0)))
            (.inst (.const 41 0)))
          (.move 1 [(45, 33)]))) => true
  | _ => false

def returningHandlerGuard : Bool :=
  match (wordFullSsaCcTrans 2 returningHandlerProgram).2.2 with
  | .seq (.move 1 [(13, 0), (17, 2)])
      (.seq (.move 0 [])
        (.seq (.move 1 [(2, 13), (4, 17)])
          (.call (some ([2, 4], ([], []), returnBody, 9, 10))
            (some 7) [2, 4]
            (some (2, exceptionBody, 11, 12))))) =>
      returningHandlerReturnShape returnBody &&
        returningHandlerExceptionShape exceptionBody
  | _ => false

#guard returningHandlerGuard

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
    noReturnEmptyCallGuard && noReturnEmptyHandlerCallGuard &&
    productionNoReturnEmptyCallGuard && productionAfterDeadNoReturnEmptyCallGuard &&
    handlerCallGuard && returningHandlerGuard

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
      ("production Cake allocator retains empty return-free Call SSA shape",
        productionNoReturnEmptyCallGuard),
      ("production Cake dead pass retains the effectful empty Call",
        productionAfterDeadNoReturnEmptyCallGuard),
      ("full_ssa_cc_trans handler Call preserves Cake exception payload",
        handlerCallGuard),
      ("full_ssa_cc_trans returning handler Call preserves both carriers",
        returningHandlerGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaCallParity
