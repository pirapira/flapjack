import Flapjack.RiscV.CakeRegAlloc

/-!
# Cake register-allocation stack-only analysis parity

Mirrors of the `word_alloc$get_stack_only` probe fixtures in
`scripts/hol-probes/get_stack_only_probeScript.sml` (oracle outputs in
`get_stack_only_probe.out`, from
`cakeml/compiler/backend/word_allocScript.sml:1741-1789`) and of the
`reg_alloc$mk_bij` / `list_remap` fixtures in
`scripts/hol-probes/mk_bij_probeScript.sml` (oracle outputs in
`mk_bij_probe.out`, from
`cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1096-1130`).

Bead `flapjack-pxn.8.5.14.1.3` (frame occupancy and allocator temporary
slots), driver slices 1 and 3.  The forced-pair analysis (`get_forced`) is
covered by `Flapjack.Test.CakeForcedParity` on the coordinator side.
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

/-- Canonical form for comparing node bijections with the probed sptree
    outputs: both maps sorted by key. -/
def sortBijectionMaps (bijection : CakeNodeBijection) :
    List (Nat × Nat) × List (Nat × Nat) :=
  (bijection.toAllocator.mergeSort (fun a b => a.1 < b.1),
   bijection.fromAllocator.mergeSort (fun a b => a.1 < b.1))

/-- Reads are remapped before writes: 2, 3 then 1. -/
def bijDeltaBasicGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.delta [1] [2, 3] : WordClashTree)) =
    ([(1, 2), (2, 0), (3, 1)], [(0, 2), (1, 3), (2, 1)]) &&
  (cakeMkBij (.delta [1] [2, 3] : WordClashTree)).nextNode = 3

/-- Already-mapped names are skipped: the write of 2 adds no node. -/
def bijDeltaDedupGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.delta [2] [2, 3] : WordClashTree)) =
    ([(2, 0), (3, 1)], [(0, 2), (1, 3)]) &&
  (cakeMkBij (.delta [2] [2, 3] : WordClashTree)).nextNode = 2

/-- `Seq` remaps the right subtree first: 7 before 5. -/
def bijSeqOrderGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.seq (.delta [] [5] : WordClashTree) (.delta [] [7] : WordClashTree))) =
    ([(5, 1), (7, 0)], [(0, 7), (1, 5)])

/-- `Branch` remaps the left subtree, then the right subtree. -/
def bijBranchOrderGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.branch none (.delta [] [9] : WordClashTree) (.delta [] [11] : WordClashTree))) =
    ([(9, 0), (11, 1)], [(0, 9), (1, 11)])

/-- The optional live set is remapped after both subtrees. -/
def bijBranchLiveGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.branch (some [13]) (.delta [] [9] : WordClashTree)
      (.delta [] [11] : WordClashTree))) =
    ([(9, 0), (11, 1), (13, 2)], [(0, 9), (1, 11), (2, 13)]) &&
  (cakeMkBij
    (.branch (some [13]) (.delta [] [9] : WordClashTree)
      (.delta [] [11] : WordClashTree))).nextNode = 3

/-- `Set` remaps its fixed name list; the sptree original always walks
    ascending keys, so an unsorted list is normalized at the boundary. -/
def bijSetGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.set [3, 4] : WordClashTree)) =
    ([(3, 0), (4, 1)], [(0, 3), (1, 4)])

/-- Unsorted `Set` input still numbers ascending, matching the sptree
    iteration of the original (cake `Set` has no order to violate). -/
def bijSetUnsortedGuard : Bool :=
  sortBijectionMaps (cakeMkBij (.set [4, 3] : WordClashTree)) =
    ([(3, 0), (4, 1)], [(0, 3), (1, 4)])

/-- Composite tree: the branch (with live set) runs first, then the delta. -/
def bijCompositeGuard : Bool :=
  sortBijectionMaps (cakeMkBij
    (.seq (.delta [1] [2] : WordClashTree)
      (.branch (some [6]) (.delta [] [4] : WordClashTree)
        (.delta [] [5] : WordClashTree)))) =
    ([(1, 4), (2, 3), (4, 0), (5, 1), (6, 2)],
     [(0, 4), (1, 5), (2, 6), (3, 2), (4, 1)]) &&
  (cakeMkBij
    (.seq (.delta [1] [2] : WordClashTree)
      (.branch (some [6]) (.delta [] [4] : WordClashTree)
        (.delta [] [5] : WordClashTree)))).nextNode = 5

def parityGuard : Bool :=
  moveChainGuard && moveFromRegGuard && seqMovesGuard && ifMergeGuard &&
    ifMergeAllocGuard && callMergeGuard && callTailGuard && assignLeafGuard &&
    bijDeltaBasicGuard && bijDeltaDedupGuard && bijSeqOrderGuard &&
    bijBranchOrderGuard && bijBranchLiveGuard && bijSetGuard &&
    bijSetUnsortedGuard && bijCompositeGuard

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    moveChainGuard, moveFromRegGuard, seqMovesGuard, ifMergeGuard,
    ifMergeAllocGuard, callMergeGuard, callTailGuard, assignLeafGuard,
    bijDeltaBasicGuard, bijDeltaDedupGuard, bijSeqOrderGuard,
    bijBranchOrderGuard, bijBranchLiveGuard, bijSetGuard,
    bijSetUnsortedGuard, bijCompositeGuard]
  let names := [
    "get_stack_only move chain", "get_stack_only move from reg",
    "get_stack_only seq moves", "get_stack_only if merge",
    "get_stack_only if merge alloc", "get_stack_only call merge",
    "get_stack_only call tail", "get_stack_only assign leaf",
    "mk_bij delta basic", "mk_bij delta dedup", "mk_bij seq order",
    "mk_bij branch order", "mk_bij branch live", "mk_bij set",
    "mk_bij set unsorted", "mk_bij composite"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CakeRegAlloc
