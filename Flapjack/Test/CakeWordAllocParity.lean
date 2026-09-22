import Flapjack.RiscV.CakeRegAlloc

/-!
# Direct Cake `word_alloc` output parity

The post-SSA two-register add below is copied from
`scripts/hol-probes/word_alloc_add1_probeScript.sml`.  The expected shape is
the checked `word_alloc_add1_probe.out` result from Cake's
`word_allocScript.sml`: the entry move is coloured to `(0,0),(2,2),(4,4)`,
the two source moves retain colours 4 and 2, and the add/return use those
colours.  This exercises the production CakeRegAlloc driver directly rather
than a hand-built allocator state.
-/

namespace Flapjack.Test.CakeWordAllocParity

open Flapjack
open Flapjack.RiscV
open Flapjack.RiscV.CakeRegAlloc

def add1Program : WordProg Nat :=
  .seq
    (.move 1 [(13, 0), (17, 2), (21, 4)])
    (.seq
      (.seq
        (.move 0 [(25, 21)])
        (.seq
          (.move 0 [(29, 17)])
          (.inst (.arith (.binOp .add 33 25 (.reg 29))))))
      (.seq (.move 0 [(2, 33)]) (.return 13 [2])))

/-! This mirrors Cake's `word_alloc 5 riscv_config 3 22` after the source
    has already passed `full_ssa_cc_trans`; the direct allocator result is
    then compared structurally with the checked HOL output above. -/
def cakeWordAllocAdd1 : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 3 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .irc scost 22 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def add1AllocatorGuard : Bool :=
  match cakeWordAllocAdd1 with
  | some
      (.seq (.move 1 [(0, 0), (2, 2), (4, 4)])
        (.seq
          (.seq (.move 0 [(4, 4)])
            (.seq (.move 0 [(2, 2)])
              (.inst (.arith (.binOp .add 2 4 (.reg 2))))))
          (.seq (.move 0 [(2, 2)]) (.return 0 [2])))) => true
  | _ => false

#guard add1AllocatorGuard

def runChecks : IO Bool := do
  if add1AllocatorGuard then
    IO.println "PASS Cake word_alloc add1 output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc add1 output matches the checked HOL oracle"
  pure add1AllocatorGuard

end Flapjack.Test.CakeWordAllocParity
