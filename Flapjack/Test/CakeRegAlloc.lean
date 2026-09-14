import Flapjack.RiscV.CakeRegAlloc

/-!
# Cake register-allocation stack-only analysis parity

Mirrors of the `word_alloc$get_stack_only` probe fixtures in
`scripts/hol-probes/get_stack_only_probeScript.sml` (oracle outputs in
`get_stack_only_probe.out`, from
`cakeml/compiler/backend/word_allocScript.sml:1741-1789`).

Bead `flapjack-pxn.8.5.14.1.3` (frame occupancy and allocator temporary
slots), driver slice 1.  The forced-pair analysis (`get_forced`) is covered
by `Flapjack.Test.CakeForcedParity` on the coordinator side.
-/

namespace Flapjack.Test.CakeRegAlloc

open Flapjack.RiscV.CakeRegAlloc

/-- Move chain whose second element writes the allocatable variable 9
    from the stack variable 7: 9 becomes forced-stack (`{9}`). -/
def moveChainGuard : Bool :=
  cakeGetStackOnly (.move 1 [(9, 9), (7, 9)] : WordProg Nat) = [9]

/-- The same move shape but sourced from physical register 2: the target
    stays allocatable (`∅`). -/
def moveFromRegGuard : Bool :=
  cakeGetStackOnly (.move 1 [(9, 9), (2, 9)] : WordProg Nat) = []

/-- Sequences thread the state right-to-left; the second move's
    forced-stack target stays visible, and the first move's plain
    delete leaves it intact (`{9}`). -/
def seqMovesGuard : Bool :=
  cakeGetStackOnly
    (.seq (.move 1 [(13, 13), (2, 13)] : WordProg Nat)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)) = [9]

/-- Branches merge the two arms; 19 is a stack variable (4n+3), so the
    right arm contributes nothing (`{9}`). -/
def ifMergeGuard : Bool :=
  cakeGetStackOnly
    (.ite .notEqual 2 (.reg 3)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)
      (.move 1 [(19, 19), (7, 19)] : WordProg Nat)) = [9]

/-- Both arms contribute allocatable targets 9 and 21 (`{9, 21}`). -/
def ifMergeAllocGuard : Bool :=
  cakeGetStackOnly
    (.ite .notEqual 2 (.reg 3)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)
      (.move 1 [(21, 21), (7, 21)] : WordProg Nat)) = [9, 21]

/-- Calls analyse and merge the return continuation and exception
    handler; 19 is a stack variable so only the continuation
    contributes (`{9}`). -/
def callMergeGuard : Bool :=
  cakeGetStackOnly
    (.call (some ([9], ([], []),
        (.move 1 [(9, 9), (7, 9)] : WordProg Nat), 0, 1))
      (some 5) [2]
      (some (11, (.move 1 [(19, 19), (7, 19)] : WordProg Nat), 0, 2))) = [9]

/-- Tail calls (no return tuple) leave the state untouched (`∅`). -/
def callTailGuard : Bool :=
  cakeGetStackOnly (.call none (some 5) [0, 2] none : WordProg Nat) = []

/-- A plain assignment is a clash-tree leaf: its written name is removed
    from the temporaries set (`∅`). -/
def assignLeafGuard : Bool :=
  cakeGetStackOnly (.assign 9 (.const 7 : WordExp Nat) : WordProg Nat) = []

def parityGuard : Bool :=
  moveChainGuard && moveFromRegGuard && seqMovesGuard && ifMergeGuard &&
    ifMergeAllocGuard && callMergeGuard && callTailGuard && assignLeafGuard

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    moveChainGuard, moveFromRegGuard, seqMovesGuard, ifMergeGuard,
    ifMergeAllocGuard, callMergeGuard, callTailGuard, assignLeafGuard]
  let names := [
    "get_stack_only move chain", "get_stack_only move from reg",
    "get_stack_only seq moves", "get_stack_only if merge",
    "get_stack_only if merge alloc", "get_stack_only call merge",
    "get_stack_only call tail", "get_stack_only assign leaf"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CakeRegAlloc
