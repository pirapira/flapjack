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

def parityGuard : Bool := returningCallGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("full_ssa_cc_trans returning Call preserves Cake return ABI",
        returningCallGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaCallParity
