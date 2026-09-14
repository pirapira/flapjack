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


/-! ## IRC graph construction guards

Structural checks for `cakeMkGraph` / `cakeExtendGraph` / `cakeMkTags` /
`cakeInitRaState`, derived from `reg_allocScript.sml`
(`sorted_insert`:184, `insert_edge`:201, `extend_clique`:235, `mk_graph`:1179,
`mk_tags`:1159).  The original threads its state through a monad over arrays,
so there is no standalone HOL oracle for the internal adjacency; the
end-to-end colouring oracle (`reg_alloc_probe.out`) validates the whole
machine once the worklist slices land. -/

private def graphAdj (tree : Flapjack.WordClashTree) (node : Nat) : List Nat :=
  let bij := Flapjack.RiscV.CakeRegAlloc.cakeMkBij tree
  let ta := Flapjack.RiscV.CakeAlloc.spDefault bij.toAllocator
  let (adj, _) := Flapjack.RiscV.CakeRegAlloc.cakeMkGraph ta tree [] []
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj node

/-- Disjoint write and read sets never clash: no edges at all. -/
def graphDeltaDisjointGuard : Bool :=
  graphAdj (.delta [1] [3]) 0 == [] && graphAdj (.delta [1] [3]) 1 == []

/-- A write clique gets one edge per pair, adjacency sorted descending. -/
def graphDeltaCliqueGuard : Bool :=
  graphAdj (.delta [1, 3] []) 0 == [1] && graphAdj (.delta [1, 3] []) 1 == [0]

/-- The fixed `Set` node is a clique over the sorted members. -/
def graphSetCliqueGuard : Bool :=
  graphAdj (.set [4, 3]) 0 == [1] && graphAdj (.set [4, 3]) 1 == [0]

/-- Forced edges are added through the same bijection (vars 1 and 3
    are bijection members here: nodes 1 and 0). -/
def graphForcedEdgeGuard : Bool :=
  let bij := Flapjack.RiscV.CakeRegAlloc.cakeMkBij (.delta [1] [3])
  let ta := Flapjack.RiscV.CakeAlloc.spDefault bij.toAllocator
  let adj := Flapjack.RiscV.CakeRegAlloc.cakeExtendGraph ta [(1, 3)] []
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 1 == [0]

/-- Tagging: allocatable variable 9 -> Atemp, stack-only 13 -> Stemp,
physical 2 -> Fixed 1. -/
def graphTagsGuard : Bool :=
  let tags := Flapjack.RiscV.CakeRegAlloc.cakeMkTags 3 [(0, 9), (1, 13), (2, 2)]
    [13]
  Flapjack.RiscV.CakeRegAlloc.cakeMapLookup tags 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup tags 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup tags 2 ==
      some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1)

/-- `init_ra_state` combines the pieces: clique edge plus tags plus dim. -/
def graphInitGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 1 == [0] &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup state.nodeTag 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup state.nodeTag 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    state.dim == 2

/-- `init_alloc1_heu` on a two-node clique: the allocation temp sees the
    stack temp as unconsidered, so degree 0 lands on the simplify
    worklist and the stack temp stays out of `allocs`. -/
def heuDeltaGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 1 &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.degrees 0 == some 0 &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.degrees 1 == some 1 &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.coalesced 0 == some 0 &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.coalesced 1 == some 1 &&
    after.simpWl == [0] && after.freezeWl == [] && after.spillWl == []

/-- `init_alloc1_heu` sorts the move worklist by descending priority and
    marks the non-fixed move endpoints move-related, sending the low-degree
    allocation temp to the freeze worklist instead of simplify. -/
def heuMovesGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let moves := [(1, (0, 1)), (3, (0, 1))]
  let (_, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu moves 4 state
  after.availMovesWl == [(3, (0, 1)), (1, (0, 1))] &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.moveRelated 0 == some true &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.moveRelated 1 == some true &&
    after.freezeWl == [0] && after.simpWl == [] && after.spillWl == []

/-- `init_alloc1_heu` sends a clique of five allocation temps (degree 4)
    over the register threshold `k = 4` to the spill worklist. -/
def heuSpillGuard : Bool :=
  let state :=
    Flapjack.RiscV.CakeRegAlloc.cakeInitRaState
      (.delta [1, 5, 9, 13, 17] []) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 5 && after.spillWl.length == 5 && after.simpWl == [] &&
    after.freezeWl == []

/-- A low physical register node counts towards its neighbour's degree
    (`considered_var`) but never enters the allocation worklist itself. -/
def heuFixedDegreeGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 2] [2, 1]) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 1 &&
    Flapjack.RiscV.CakeRegAlloc.cakeMapLookup after.degrees 1 == some 1 &&
    after.simpWl == [1] && after.spillWl == []

/-- Normalise a colouring to the ascending original-variable order that the
    original sptree iteration produces. -/
def sortColouring (colours : Flapjack.NatInfoMap Nat) :
    List (Nat × Nat) :=
  colours.mergeSort (fun a b => a.1 < b.1)

/-- `sorting$PARTITION` reverses both buckets (`PART P l [] []` prepends). -/
def partOrderGuard : Bool :=
  partitionReversed (fun x => x % 2 == 0) [0, 1, 2] == ([2, 0], [1])

/-- `revive_moves` partitions the unavailable-move worklist with the
    bucket-reversing `sorting$PARTITION`. -/
def reviveOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := [(9, [5])],
      unavailMovesWl := [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))],
      availMovesWl := [(2, (1, 1))] }
  let out := Flapjack.RiscV.CakeRegAlloc.cakeReviveMoves [9] base
  out.availMovesWl == [(2, (1, 1)), (1, (5, 9)), (1, (13, 5))] &&
    out.unavailMovesWl == [(1, (13, 17))]

/-- `bg_ok` partitions `adjY` by `adjX` membership with the bucket-reversing
    `sorting$PARTITION`, then `st_ex_FILTER`s each case list. -/
def bgOkOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := [(0, [1]), (1, [3, 0]), (2, [3]), (3, [2, 1, 0])],
      nodeTag := (List.range 4).map (fun i => (i, .aTemp)) }
  Flapjack.RiscV.CakeRegAlloc.cakeBgOk 3 0 3 base == some ([1], [2, 0])

/-- `reg_alloc` on a single write/read pair colours the write with the
    first free register and the unconnected stack temp with `k`. -/
def raDeltaPairGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4)])

/-- A physical-register read keeps its own register colour (`2 ↦ 1`). -/
def raDeltaFreeGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [2]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (2, 1)])

/-- A triangle `1-3-5` needs the spill channel for one participant. -/
def raDeltaTriangleGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.seq (.delta [1] [3])
         (.seq (.delta [3] [5]) (.delta [5] [1]))) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 1)])

/-- A stack-only variable is forced to the spill channel (`k` or above). -/
def raStackOnlyGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [7] [1, 3]) [] [7]).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (7, 4)])

/-- A move between `1` and `5` coalesces both to the register colour of
    `1` (`{1 ↦ 0; 5 ↦ 0}`). -/
def raMovesCoalesceGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (1, 5))]
      (.delta [1] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 0)])

/-- A self move is filtered out by the consistency check; the colouring
    then matches the coalesced case. -/
def raMovesSelfFilteredGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (1, 1))]
      (.delta [1] [5, 3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4), (5, 0)])

/-- A forced edge `1-5` separates the two nodes onto different registers
    (`{1 ↦ 1; 5 ↦ 0}`). -/
def raForcedEdgeGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [5, 3]) [(1, 5)] []).map sortColouring ==
    some (sortColouring [(1, 1), (3, 4), (5, 0)])

def parityGuard : Bool :=
  moveChainGuard && moveFromRegGuard && seqMovesGuard && ifMergeGuard &&
    ifMergeAllocGuard && callMergeGuard && callTailGuard && assignLeafGuard &&
    bijDeltaBasicGuard && bijDeltaDedupGuard && bijSeqOrderGuard &&
    bijBranchOrderGuard && bijBranchLiveGuard && bijSetGuard &&
    bijSetUnsortedGuard && bijCompositeGuard && graphDeltaDisjointGuard &&
    graphDeltaCliqueGuard && graphSetCliqueGuard && graphForcedEdgeGuard &&
    graphTagsGuard && graphInitGuard && heuDeltaGuard && heuMovesGuard &&
    heuSpillGuard && heuFixedDegreeGuard && raDeltaPairGuard &&
    raDeltaFreeGuard && raDeltaTriangleGuard && raStackOnlyGuard &&
    raMovesCoalesceGuard && raMovesSelfFilteredGuard && raForcedEdgeGuard &&
    partOrderGuard && reviveOrderGuard && bgOkOrderGuard

#guard parityGuard
def runChecks : IO Bool := do
  let results := [
    moveChainGuard, moveFromRegGuard, seqMovesGuard, ifMergeGuard,
    ifMergeAllocGuard, callMergeGuard, callTailGuard, assignLeafGuard,
    bijDeltaBasicGuard, bijDeltaDedupGuard, bijSeqOrderGuard,
    bijBranchOrderGuard, bijBranchLiveGuard, bijSetGuard,
    bijSetUnsortedGuard, bijCompositeGuard, graphDeltaDisjointGuard,
    graphDeltaCliqueGuard, graphSetCliqueGuard, graphForcedEdgeGuard,
    graphTagsGuard, graphInitGuard, heuDeltaGuard, heuMovesGuard,
    heuSpillGuard, heuFixedDegreeGuard, raDeltaPairGuard, raDeltaFreeGuard,
    raDeltaTriangleGuard, raStackOnlyGuard, raMovesCoalesceGuard,
    raMovesSelfFilteredGuard, raForcedEdgeGuard, partOrderGuard,
    reviveOrderGuard, bgOkOrderGuard]
  let names := [
    "get_stack_only move chain", "get_stack_only move from reg",
    "get_stack_only seq moves", "get_stack_only if merge",
    "get_stack_only if merge alloc", "get_stack_only call merge",
    "get_stack_only call tail", "get_stack_only assign leaf",
    "mk_bij delta basic", "mk_bij delta dedup", "mk_bij seq order",
    "mk_bij branch order", "mk_bij branch live", "mk_bij set",
    "mk_bij set unsorted", "mk_bij composite", "mk_graph delta disjoint",
    "mk_graph delta clique", "mk_graph set clique", "extend_graph forced",
    "mk_tags roles", "init_ra_state", "init_alloc1_heu delta",
    "init_alloc1_heu moves", "init_alloc1_heu spill",
    "init_alloc1_heu fixed degree", "reg_alloc delta pair",
    "reg_alloc delta free", "reg_alloc delta triangle",
    "reg_alloc stack only", "reg_alloc moves coalesce",
    "reg_alloc moves self filtered", "reg_alloc forced edge",
    "sorting partition order", "revive moves order", "bg_ok order"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CakeRegAlloc
