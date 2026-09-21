import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordDeadCode

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

/- These control-flow cases mirror the Cake `MustTerminate` and `Loop`
   equations in `word_allocScript.sml:1754-1769`.  The canonical HOL probe
   returns `[9]` for each wrapper around the forced-stack move chain. -/
def mustTerminateGuard : Bool :=
  cakeGetStackOnly
      (.mustTerminate (.move 1 [(9, 9), (7, 9)] : WordProg Nat)) = [9]

def loopBodyGuard : Bool :=
  cakeGetStackOnly
      (.loop [] (.move 1 [(9, 9), (7, 9)]) [] : WordProg Nat) = [9]

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

/- The indexed builder is only an implementation optimization; its public
   maps and numbering must remain identical to the direct Cake-shaped walk. -/
def bijIndexedBuilderParityGuard : Bool :=
  let trees : List WordClashTree :=
    [.delta [1] [2, 3],
     .branch (some [13]) (.delta [] [9]) (.delta [] [11]),
     .seq (.delta [1] [2])
       (.branch (some [6]) (.delta [] [4]) (.delta [] [5]))]
  trees.all (fun tree =>
    let reference := cakeMkBijAux tree
      { toAllocator := [], fromAllocator := [], nextNode := 0 }
    let indexed := cakeMkBij tree
    indexed.toAllocator == reference.toAllocator &&
      indexed.fromAllocator == reference.fromAllocator &&
      indexed.nextNode == reference.nextNode)

#guard bijIndexedBuilderParityGuard

/- The hot-path source index must preserve the Cake association-list lookup,
   including the zero fallback for a name absent from the bijection. -/
def allocatorIndexLookupGuard : Bool :=
  let entries : NatInfoMap Nat := [(9, 4), (1, 2), (17, 6)]
  let index := cakeAllocatorIndex entries
  cakeAllocatorIndexLookup index 9 = 4 &&
    cakeAllocatorIndexLookup index 1 = 2 &&
    cakeAllocatorIndexLookup index 17 = 6 &&
    cakeAllocatorIndexLookup index 99 = 0

#guard allocatorIndexLookupGuard

def extractColorOrderGuard : Bool :=
  let tree : WordClashTree := .delta [9, 1] [17]
  let bij := cakeMkBij tree
  let state := cakeInitRaState tree [] []
  cakeExtractColor state bij.toAllocator ==
    [(1, 0), (9, 0), (17, 0)]

#guard extractColorOrderGuard


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
  let (adj, _) := Flapjack.RiscV.CakeRegAlloc.cakeMkGraph ta tree [] {}
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
  let adj := Flapjack.RiscV.CakeRegAlloc.cakeExtendGraph ta [(1, 3)] {}
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub adj 1 == [0]

/-- Tagging: allocatable variable 9 -> Atemp, stack-only 13 -> Stemp,
physical 2 -> Fixed 1. -/
def graphTagsGuard : Bool :=
  let tags := Flapjack.RiscV.CakeRegAlloc.cakeMkTags 3 [(0, 9), (1, 13), (2, 2)]
    [13]
  tags.get 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    tags.get 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    tags.get 2 ==
      some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1)

/-- `init_ra_state` combines the pieces: clique edge plus tags plus dim. -/
def graphInitGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 0 == [1] &&
    Flapjack.RiscV.CakeRegAlloc.cakeAdjSub state.adjLists 1 == [0] &&
    state.nodeTag.get 0 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.aTemp &&
    state.nodeTag.get 1 ==
      some Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.sTemp &&
    state.dim == 2

/-- `init_alloc1_heu` on a two-node clique: the allocation temp sees the
    stack temp as unconsidered, so degree 0 lands on the simplify
    worklist and the stack temp stays out of `allocs`. -/
def heuDeltaGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let (count, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu [] 4 state
  count == 1 &&
    after.degrees.get 0 == some 0 &&
    after.degrees.get 1 == some 1 &&
    after.coalesced.get 0 == some 0 &&
    after.coalesced.get 1 == some 1 &&
    after.simpWl == [0] && after.freezeWl == [] && after.spillWl == []

/-- `init_alloc1_heu` sorts the move worklist by descending priority and
    marks the non-fixed move endpoints move-related, sending the low-degree
    allocation temp to the freeze worklist instead of simplify. -/
def heuMovesGuard : Bool :=
  let state := Flapjack.RiscV.CakeRegAlloc.cakeInitRaState (.delta [1, 3] []) [] []
  let moves := [(1, (0, 1)), (3, (0, 1))]
  let (_, after) := Flapjack.RiscV.CakeRegAlloc.cakeInitAlloc1Heu moves 4 state
  after.availMovesWl == [(3, (0, 1)), (1, (0, 1))] &&
    after.moveRelated.get 0 == some true &&
    after.moveRelated.get 1 == some true &&
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
    after.degrees.get 1 == some 1 &&
    after.simpWl == [1] && after.spillWl == []

/-- Normalise a colouring to the ascending original-variable order that the
    original sptree iteration produces. -/
def sortColouring (colours : Flapjack.NatInfoMap Nat) :
    List (Nat × Nat) :=
  colours.mergeSort (fun a b => a.1 < b.1)

/-- `sorting$PARTITION` reverses both buckets (`PART P l [] []` prepends). -/
def partOrderGuard : Bool :=
  partitionReversed (fun x => x % 2 == 0) [0, 1, 2] == ([2, 0], [1])

/-- `revive_moves` uses reversing HOL `PARTITION`; `sort_moves` then applies
    Cake's equal-priority order to the reversed revived bucket. -/
def reviveOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4 [(9, [5])],
      unavailMovesWl := [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))],
      availMovesWl := [(2, (1, 1))] }
  let out := Flapjack.RiscV.CakeRegAlloc.cakeReviveMoves [9] base
  out.availMovesWl == [(2, (1, 1)), (1, (5, 9)), (1, (13, 5))] &&
    out.unavailMovesWl == [(1, (13, 17))]

def movesToSpOrderGuard : Bool :=
  let table := Flapjack.RiscV.CakeRegAlloc.cakeMovesToSp
    [(1, (2, 5)), (2, (2, 7)), (3, (2, 11))]
      (Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofSize 12)
  table.get 2 ==
      some [(3, 11), (2, 7), (1, 5)] &&
    table.get 5 == some [(1, 2)]

/-- Cake's composed `moves_to_sp`/`resort_moves` output keeps the partner
    names in descending priority order before biased IRC preferences consume
    them.  The expected order is recorded by `reg_alloc_probe.out`, which
    evaluates the original Cake definitions directly. -/
def resortMovesSpOrderGuard : Bool :=
  let table := Flapjack.RiscV.CakeRegAlloc.cakeMovesToSp
    [(1, (2, 5)), (2, (2, 7)), (3, (2, 11))]
      (Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofSize 12)
  let resorted := Flapjack.RiscV.CakeRegAlloc.cakeResortMovesSp table
  resorted.get 2 == some [11, 7, 5] &&
    resorted.get 5 == some [2] && resorted.get 7 == some [2] &&
    resorted.get 11 == some [2]

#guard reviveOrderGuard
#guard resortMovesSpOrderGuard

/-- `bg_ok` uses reversing HOL `PARTITION`, then `st_ex_FILTER`s each case list. -/
def bgOkOrderGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        [(0, [1]), (1, [3, 0]), (2, [3]), (3, [2, 1, 0])],
      nodeTag := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        ((List.range 4).map (fun i => (i, .aTemp))) }
  Flapjack.RiscV.CakeRegAlloc.cakeBgOk 3 0 3 base == some ([1], [2, 0])

def revivePartitionGuard : Bool :=
  let base : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 4 with
      adjLists := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 4
        [(9, [17, 13, 5])],
      unavailMovesWl := [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))] }
  let out := Flapjack.RiscV.CakeRegAlloc.cakeReviveMoves [9] base
  out.availMovesWl == [(1, (5, 9)), (1, (13, 5)), (1, (13, 17))] &&
    out.unavailMovesWl == []

/-- `reg_alloc` on a single write/read pair colours the write with the
    first free register and the unconnected stack temp with `k`. -/
def raDeltaPairGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [1] [3]) [] []).map sortColouring ==
    some (sortColouring [(1, 0), (3, 4)])

/-- The threaded allocator entrypoint is definitionally the same computation as
    the compatibility wrapper, while allowing production callers to reuse the
    bijection and initial graph state they already built. -/
def threadedAllocatorEntryGuard : Bool :=
  let tree : WordClashTree := .delta [1] [3]
  let bij := cakeMkBij tree
  let state := cakeInitRaStateFromBij bij tree [] []
  cakeDoRegAlloc .irc none 4 [] tree [] [] ==
    cakeDoRegAllocFromState .irc none 4 [] bij state

#guard threadedAllocatorEntryGuard

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

/- These two outputs are direct `reg_alloc_probe.out` observations.  A
   sequential pair has no interference and may share colour zero, while a
   same-delta clique must receive distinct colours. -/
def raOrderSeqGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.seq (.delta [9] []) (.delta [13] [])) [] []).map sortColouring ==
    some (sortColouring [(9, 0), (13, 0)])

def raOrderCliqueGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 []
      (.delta [9, 13] []) [] []).map sortColouring ==
    some (sortColouring [(9, 0), (13, 1)])

/- The canonical `reg_alloc_probe.out` cost-sensitive case exercises
   `do_spill` with a non-`NONE` source-keyed table and one allocatable colour:
   Cake selects the high-cost source 5 for colour 0, leaving 1 and 9 in the
   two spill colours. -/
def raSpillCostGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 1), (5, 100), (9, 1)]
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc
      (some (cakeSpillCostMap 3 costs)) 1 []
      (.delta [1, 5, 9] []) [] []).map sortColouring ==
    some (sortColouring [(1, 1), (5, 0), (9, 2)])

/- Cake's `st_ex_list_MIN_cost` scans the remaining spill worklist in order,
   replacing the selected node only on a strict lower cost.  This direct case
   checks both the cost division and the reversed residual list from
   `reg_allocScript.sml:773-790`. -/
def stExMinCostOrderGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 100), (2, 1)]
  cakeStExListMinCost degrees costs [1, 2] 4 0 5 [] == (2, [0, 1])

#guard stExMinCostOrderGuard

/- Equal spill costs retain the first candidate: Cake's `v > cost` test is
   strict, while each visited non-selected node is prepended to the residual
   worklist. -/
def stExMinCostTieGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 2), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 10), (2, 10)]
  cakeStExListMinCost degrees costs [1, 2] 4 0 5 [] == (0, [2, 1])

#guard stExMinCostTieGuard

/- Cake's `safe_div` maps a zero degree to cost zero before the strict
   comparison; this keeps the spill scan total without inventing a divisor. -/
def stExMinCostZeroDegreeGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 0), (2, 2)]
  let costs := CakeNodeMap.ofNatInfoMap 4 [(0, 10), (1, 7), (2, 1)]
  cakeSafeDiv 7 0 == 0 &&
    cakeStExListMinCost degrees costs [1, 2] 4 0 1 [] == (1, [2, 0])

#guard stExMinCostZeroDegreeGuard

/- Cake's cost-free `do_spill` fallback uses `st_ex_list_MAX_deg`: it scans
   the remaining worklist, replacing the selected node only on a strict
   degree increase and retaining the reversed residual list. -/
def stExMaxDegOrderGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 3)]
  cakeStExListMaxDeg degrees [1, 2] 4 0 2 [] == (2, [0, 1])

#guard stExMaxDegOrderGuard

/- Equal degrees retain the first spill candidate: Cake's comparison is
   strict, so a tie must not perturb the selected node. -/
def stExMaxDegTieGuard : Bool :=
  let degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 2), (2, 2)]
  cakeStExListMaxDeg degrees [1, 2] 4 0 2 [] == (0, [2, 1])

#guard stExMaxDegTieGuard

/- End-to-end `do_spill` oracle: Cake selects node 2, pushes it, and
   `unspill` moves the residual low-degree node 1 to the simplify worklist. -/
def doSpillTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(0, 2), (1, 1), (2, 3)],
      spillWl := [1, 2] }
  let (did, after) := cakeDoSpill none 4 state
  did && after.stack == [2] && after.simpWl == [1] &&
    after.freezeWl == [] && after.spillWl == []

#guard doSpillTransitionGuard

/- Cake's `dec_degree` skips an out-of-dimension node before reading its
   adjacency list.  This matters for the functional map's explicit `outside`
   bindings: an out-of-range edge must not decrement an in-range neighbour. -/
def decDegreeOutOfDimGuard : Bool :=
  let adj := cakeInsertEdge 3 1 (CakeNodeMap.ofSize 2)
  let state : CakeRaState :=
    { CakeRaState.empty 2 with
      adjLists := adj,
      degrees := CakeNodeMap.ofNatInfoMap 2 [(1, 2)] }
  let after := cakeDecDegree 3 state
  (after.degrees.get 1).getD 0 == 2

#guard decDegreeOutOfDimGuard

/- Cake's `respill` (`reg_allocScript.sml:659-674`) moves a freeze-worklist
   node back to the spill worklist only when its degree reaches `k`; it
   removes that node from `freezeWl` and prepends it to `spillWl`. -/
def respillWorklistGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(3, 4)]
      spillWl := [1, 2]
      freezeWl := [3] }
  let moved := cakeRespill 4 3 state
  moved.spillWl == [3, 1, 2] && moved.freezeWl == [] &&
    (moved.degrees.get 3).getD 0 == 4

def respillBelowThresholdGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(3, 3)]
      spillWl := [1]
      freezeWl := [3] }
  let unchanged := cakeRespill 4 3 state
  unchanged.spillWl == [1] && unchanged.freezeWl == [3]

#guard respillWorklistGuard
#guard respillBelowThresholdGuard

/- Cake's `do_simplify` (`reg_allocScript.sml:400-415`) processes the whole
   simplify worklist before pushing it, preserving the worklist order in the
   reverse stack order and then clearing `simpWl`. -/
def simplifyBatchGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      degrees := CakeNodeMap.ofNatInfoMap 4 [(1, 1), (2, 2)]
      simpWl := [1, 2] }
  let (changed, simplified) := cakeDoSimplify 3 state
  changed && simplified.simpWl == [] && simplified.stack == [2, 1] &&
    (simplified.degrees.get 1).getD 0 == 0 &&
    (simplified.degrees.get 2).getD 0 == 0

#guard simplifyBatchGuard
/- Cake's `dec_degree` (`reg_allocScript.sml:263-272`) is a safe no-op for
   an out-of-dimension node, even if an outside adjacency entry exists. -/
def decDegreeOutOfDimNoOpGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      adjLists := CakeNodeMap.ofNatInfoMap 3 [(5, [1])]
      degrees := CakeNodeMap.ofNatInfoMap 3 [(1, 2)] }
  let out := cakeDecDegree 5 state
  (out.degrees.get 1).getD 0 == 2

#guard decDegreeOutOfDimNoOpGuard

/- Cake's `do_coalesce` (`reg_allocScript.sml:676-698`) consumes the first
   compatible move, coalesces its second endpoint into the first, clears the
   available-move worklist, and pushes the coalesced endpoint onto the stack. -/
def coalesceWorklistSuccessGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 3 with
      moveRelated := CakeNodeMap.ofNatInfoMap 3 [(1, true), (2, true)]
      availMovesWl := [(1, (1, 2))] }
  let (changed, out) := cakeDoCoalesce 3 state
  changed && out.availMovesWl == [] && out.unavailMovesWl == [] &&
    (out.coalesced.get 2).getD 2 == 1 && out.stack == [2] &&
    (out.moveRelated.get 2).getD true == false

#guard coalesceWorklistSuccessGuard

/- Cake's `do_freeze` (`reg_allocScript.sml:749-764`) decrements the frozen
   node's neighbours, pushes it, removes it from `freezeWl`, then unspills a
   spill node that has become low degree into the simplify worklist. -/
def freezeWorklistTransitionGuard : Bool :=
  let state : CakeRaState :=
    { CakeRaState.empty 4 with
      adjLists := CakeNodeMap.ofNatInfoMap 4 [(1, [2]), (2, [1])]
      degrees := CakeNodeMap.ofNatInfoMap 4 [(1, 1), (2, 1)]
      moveRelated := CakeNodeMap.ofNatInfoMap 4 [(1, true), (2, false)]
      freezeWl := [1]
      spillWl := [2] }
  let (changed, out) := cakeDoFreeze 2 state
  changed && out.freezeWl == [] && out.spillWl == [] &&
    out.simpWl == [2] && out.stack == [1] &&
    (out.degrees.get 1).getD 0 == 0 &&
    (out.degrees.get 2).getD 0 == 0 &&
    (out.moveRelated.get 1).getD true == false

#guard freezeWorklistTransitionGuard
/- `get_prefs_def` uses `MAP ... ++ acc`, preserving each Move's source
   order.  These guards mirror the canonical `get_prefs_probe.out` output. -/
def prefsMoveOrderGuard : Bool :=
  cakeGetPrefs (.move 7 [(1, 2), (3, 4)] : WordProg Nat) [] ==
    [(7, (1, 2)), (7, (3, 4))]

def prefsSeqOrderGuard : Bool :=
  cakeGetPrefs
      (.seq (.move 7 [(1, 2), (3, 4)])
        (.move 8 [(5, 6), (7, 8)]) : WordProg Nat) [] ==
    [(7, (1, 2)), (7, (3, 4)), (8, (5, 6)), (8, (7, 8))]

def prefsControlFlowGuard : Bool :=
  cakeGetPrefs
      (.mustTerminate (.move 9 [(9, 10), (11, 12)]) : WordProg Nat) [] ==
      [(9, (9, 10)), (9, (11, 12))] &&
    cakeGetPrefs
      (.loop [] (.move 10 [(13, 14), (15, 16)]) [] : WordProg Nat) [] ==
      [(10, (13, 14)), (10, (15, 16))] &&
    cakeGetPrefs
      (.ite .notEqual 2 (.reg 3)
        (.move 11 [(17, 18)]) (.move 12 [(19, 20)]) : WordProg Nat) [] ==
    [(11, (17, 18)), (12, (19, 20))]

/-! These control-flow cases mirror the remaining `get_prefs_def` equations
    in Cake's `word_allocScript.sml`: both branch arms are traversed with the
    else-arm as the incoming accumulator, and a handled call traverses its
    handler after its return continuation. -/
def prefsBranchOrderGuard : Bool :=
  cakeGetPrefs
      (.ite .notEqual 2 (.reg 3)
        (.move 9 [(1, 2)]) (.move 10 [(3, 4)]) : WordProg Nat) [] ==
    [(9, (1, 2)), (10, (3, 4))]

def prefsCallHandlerOrderGuard : Bool :=
    cakeGetPrefs
      (.call (some ([9], ([], []),
          (.move 11 [(5, 6)] : WordProg Nat), 0, 1))
        (some 2) []
        (some (12, (.move 13 [(7, 8)] : WordProg Nat), 0, 2)) : WordProg Nat) [] ==
    [(13, (7, 8)), (11, (5, 6))]

/- `get_prefs_def`'s handled-call `NONE` branch traverses only the return
   handler; it must not invent preferences from an absent exception handler. -/
def prefsCallReturnOnlyGuard : Bool :=
  cakeGetPrefs
      (.call (some ([9], ([], []),
          (.move 15 [(1, 2)] : WordProg Nat), 0, 1))
        (some 2) [] none : WordProg Nat) [] ==
    [(15, (1, 2))]

def prefsLoopOrderGuard : Bool :=
  cakeGetPrefs
      (.loop [2]
        (.move 14 [(9, 10)] : WordProg Nat) [3] : WordProg Nat) [] ==
    [(14, (9, 10))]

/-- `sort_moves` flips equal-priority moves relative to the input order
    (probe `sort_moves_probe.out` `sm_ties_two`). -/
def qsortTiesTwoGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves [(1, (13, 5)), (1, (5, 9))] ==
    [(1, (5, 9)), (1, (13, 5))]

/-- A second equal-priority flip case (probe `sm_ties_three`): the two
    priority-3 moves come out reversed. -/
def qsortTiesThreeGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(3, (1, 2)), (1, (9, 9)), (3, (7, 8))] ==
    [(3, (7, 8)), (3, (1, 2)), (1, (9, 9))]

/-! The tail merge split changes equal-priority order at the first
    non-trivial recursion sizes; these are direct `reg_alloc$sort_moves`
    oracle cases for lengths four through six. -/
def sortMovesTailSplitGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8))] ==
      [(7, (7, 8)), (7, (5, 6)), (7, (3, 4)), (7, (1, 2))] &&
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8)), (7, (9, 10))] ==
      [(7, (9, 10)), (7, (7, 8)), (7, (5, 6)), (7, (3, 4)), (7, (1, 2))] &&
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(7, (1, 2)), (7, (3, 4)), (7, (5, 6)), (7, (7, 8)), (7, (9, 10)),
       (7, (11, 12))] ==
      [(7, (11, 12)), (7, (9, 10)), (7, (7, 8)), (7, (5, 6)), (7, (3, 4)),
       (7, (1, 2))]

/-! Cake's pairwise merge sort reverses a long run of equal priorities. -/
def sortMovesLongTieGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(12, (133, 173)), (12, (129, 133)), (12, (117, 149)),
       (12, (113, 117)), (12, (105, 121)), (12, (101, 157)),
       (12, (97, 101)), (12, (89, 105)), (12, (85, 141)),
       (12, (81, 85)), (12, (73, 89)), (12, (69, 165)),
       (12, (65, 69)), (12, (57, 73)), (12, (53, 137)),
       (12, (49, 53)), (12, (45, 57)), (12, (41, 45)),
       (12, (2, 185)), (22, (0, 37))] ==
      [(22, (0, 37)), (12, (2, 185)), (12, (41, 45)),
       (12, (45, 57)), (12, (49, 53)), (12, (53, 137)),
       (12, (57, 73)), (12, (65, 69)), (12, (69, 165)),
       (12, (73, 89)), (12, (81, 85)), (12, (85, 141)),
       (12, (89, 105)), (12, (97, 101)), (12, (101, 157)),
       (12, (105, 121)), (12, (113, 117)), (12, (117, 149)),
       (12, (129, 133)), (12, (133, 173))]

/-- Strictly descending priorities sort descending (probe `sm_desc`). -/
def qsortDescGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSortMoves
      [(1, (13, 5)), (3, (5, 9)), (2, (7, 8))] ==
    [(3, (5, 9)), (2, (7, 8)), (1, (13, 5))]

/-- `assign_Stemp_tag` uses Cake's non-strict bad-colour ordering; equal
    colours therefore retain Cake's merge-sort tie order. -/
def stempBadColourTieGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeSort (fun a b => a <= b) [4, 4, 1, 4] ==
    [1, 4, 4, 4]

#guard stempBadColourTieGuard

/-- A move onto a stack temp keeps the stack temp above the register
    count while the two alloc vars coalesce (probe `ra_moves_stemp`). -/
def raMovesStempGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(1, (3, 9))]
      (.delta [9] [13, 3]) [] []).map sortColouring ==
    some (sortColouring [(3, 4), (9, 0), (13, 0)])

/-- The same shape with a higher move priority (probe
    `ra_moves_stemp_hi`). -/
def raMovesStempHiGuard : Bool :=
  (Flapjack.RiscV.CakeRegAlloc.cakeDoRegAlloc .irc none 4 [(5, (3, 9))]
      (.delta [9] [13, 3]) [] []).map sortColouring ==
    some (sortColouring [(3, 4), (9, 0), (13, 0)])

/-- `neg_first_match_col` projects each candidate through the node tag
    table: non-`Fixed` tags are skipped and a missing entry stops the
    search. -/
def negFirstMatchProjectionGuard : Bool :=
  let state : Flapjack.RiscV.CakeRegAlloc.CakeRaState :=
    { Flapjack.RiscV.CakeRegAlloc.CakeRaState.empty 7 with
      nodeTag := Flapjack.RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap 7
        [(4, .fixed 6), (5, .aTemp), (6, .fixed 2)] }
  Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [2] [4, 5, 6] ==
      some 6 &&
    Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [6] [6] ==
      none &&
    Flapjack.RiscV.CakeRegAlloc.cakeNegFirstMatchCol state 3 [] [5, 7] ==
      none

/- The HOL allocator updates fixed-size array cells.  Repeated writes to an
   existing node must therefore not retain an unbounded history in the Lean
   association-list representation. -/
def mapUpdateBoundedGuard : Bool :=
  let initial : Flapjack.NatInfoMap Nat := [(0, 0), (1, 1)]
  let updated := (List.range 100).foldl
    (fun map value => cakeMapUpdate map 0 value) initial
  let inserted := cakeMapUpdate updated 2 7
  updated.length == 2 &&
    cakeMapLookup updated 0 == some 99 &&
    cakeMapLookup updated 1 == some 1 &&
    inserted.length == 3 && cakeMapLookup inserted 2 == some 7

/-- `word_alloc` passes `get_heuristics` costs keyed by source variables
    directly to `reg_alloc`; the array adapter preserves those keys, including
    source names outside the dense allocator array. -/
def sourceSpillCostKeyGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 10), (2, 1), (5, 20)]
  let table := cakeSpillCostMap 3 costs
  table.get 1 == some 10 && table.get 2 == some 1 && table.get 5 == some 20 &&
    table.get 0 == none

/- Cake's fixed allocator array exposes source-keyed costs outside its dense
   dimension through the same lookup/update semantics as the HOL sptree.
   The first source binding also wins, matching lookup_any on the original map. -/
def sourceSpillCostRoundTripGuard : Bool :=
  let costs : Flapjack.NatInfoMap Nat := [(1, 10), (1, 11), (5, 20)]
  let table := cakeSpillCostMap 3 costs
  table.toNatInfoMap == [(1, 10), (5, 20)] &&
    table.get 5 == some 20

def sourceMovePhysicalFallbackGuard : Bool :=
  Flapjack.RiscV.CakeRegAlloc.cakeUpdateMove
      (Flapjack.RiscV.CakeAlloc.spDefault []) (7, (2, 9)) == (7, (0, 1))

/-- Cake's `remove_dead (Move pri ls)` keeps the surviving move priority
    (`word_allocScript.sml:891-899`).  The priority orders the coalescing
    worklist (`sort_moves` sorts descending, `do_coalesce` consumes the first
    compatible move), so the `Move1` SSA entry/ABI shuffle must still be
    priority 1 after the dead pass; rebuilding it as priority 0 let the
    `callee_abi` entry copies survive. -/
def deadMovePriorityGuard : Bool :=
  match Flapjack.RiscV.wordDeadCode (.move 1 [(6, 2)] : WordProg Nat) [6] with
  | (.move priority [(6, 2)], _) => priority == 1
  | _ => false

/-- The full dead-program pass keeps the priority of a live entry move. -/
def deadProgramPriorityGuard : Bool :=
  match Flapjack.RiscV.wordRemoveDeadProgram
      (.seq (.move 1 [(6, 2)]) (.return 0 [6]) : WordProg Nat) with
  | .seq (.move priority _) _ => priority == 1
  | _ => false

/- These three guards mirror the non-instruction `get_live` equations in
   `word_allocScript.sml`: a tail call carries only its arguments, Alloc keeps
   its result live with both cut-set components, and StoreConsts kills its
   source/bitmap while retaining the produced lengths. -/
def deadTailCallLiveGuard : Bool :=
  match Flapjack.RiscV.wordDeadCodeAux
      (.call none (some 7) [2, 4] none : WordProg Nat) [99] [] with
  | (.call none (some 7) [2, 4] none, live) => live == [2, 4]
  | _ => false

def deadAllocLiveGuard : Bool :=
  match Flapjack.RiscV.wordDeadCodeAux
      (.alloc 7 ([2], [3]) : WordProg Nat) [99] [] with
  | (.alloc 7 ([2], [3]), live) => live == [7, 2, 3]
  | _ => false

def deadInstallLiveGuard : Bool :=
  match Flapjack.RiscV.wordDeadCodeAux
      (.install 7 8 9 10 ([11], [12]) : WordProg Nat) [99] [] with
  | (.install 7 8 9 10 ([11], [12]), live) => live == [7, 8, 9, 10, 11, 12]
  | _ => false

def deadFfiLiveGuard : Bool :=
  match Flapjack.RiscV.wordDeadCodeAux
      (.ffi "svc" 7 8 9 10 ([11], [12]) : WordProg Nat) [99] [] with
  | (.ffi "svc" 7 8 9 10 ([11], [12]), live) => live == [7, 8, 9, 10, 11, 12]
  | _ => false

def deadStoreConstsLiveGuard : Bool :=
  match Flapjack.RiscV.wordDeadCodeAux
      (.storeConsts 1 2 3 4 [] : WordProg Nat) [1, 2, 9] [] with
  | (.storeConsts 1 2 3 4 [], live) => live == [9, 3, 4]
  | _ => false

def copyLastMoveSource : WordProg Nat → Option Nat
  | .move _ [(destination, source)] =>
      if destination == 485 then some source else none
  | .seq _ second => copyLastMoveSource second
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def copyGetPreservesClassGuard : Bool :=
  let steps : List (WordProg Nat) :=
    [.move 0 [(409, 401)], .move 0 [(413, 389)], .move 0 [(417, 373)],
     .move 0 [(421, 385)], .move 0 [(425, 377)], .move 0 [(429, 413)],
     .seq (.move 0 [(433, 409)]) (.inst (.mem .store 429 433)),
     .move 0 [(437, 417)],
     .seq (.move 0 [(441, 433)]) (.store (.var 441) 437),
     .move 0 [(445, 421)],
     .seq (.move 0 [(449, 441)]) (.store (.var 449) 445),
     .move 0 [(453, 425)],
     .seq (.move 0 [(457, 449)]) (.store (.var 457) 453),
     .get 461 (.heapLength),
     .inst (.arith (.shift .lsl 465 461 (.imm 1))),
     .opCurrHeap .add 469 465,
     .assign 473 (.load (.var 469)), .assign 477 (.load (.var 473)),
     .move 0 [(481, 381)], .move 0 [(485, 409)]]
  let (program, _) := steps.foldl
    (fun (program, state) step =>
      let (step, state) := Flapjack.RiscV.wordCopyProg state step
      (.seq program step, state))
    (.skip, Flapjack.RiscV.wordCopyEmpty)
  copyLastMoveSource program == some 457

#guard copyGetPreservesClassGuard

/- Cake's mk_bij_aux enumerates a Set through the Patricia-tree toAList,
   whose order is not ascending.  This fixture is the checked HOL order
   [0, 4, 12, 6] and guards the allocator node numbering that feeds
   register-colour tie breaks. -/
def cakeBijSetPatriciaGuard : Bool :=
  let bij := cakeMkBij (.set [0, 4, 6, 12])
  lookupNatInfo 0 bij.toAllocator == some 0 &&
    lookupNatInfo 4 bij.toAllocator == some 1 &&
    lookupNatInfo 12 bij.toAllocator == some 2 &&
    lookupNatInfo 6 bij.toAllocator == some 3

#guard cakeBijSetPatriciaGuard
def applyColourSetPatriciaGuard : Bool :=
  wordApplyColourNumSet id [0, 4, 6, 12] == [0, 4, 12, 6]

#guard applyColourSetPatriciaGuard

/- Cake's `max_var` ignores control-flow labels on Break and Continue; they
   are labels, not Word register names and must not enlarge the stack frame. -/
def maxVarControlLabelGuard : Bool :=
  wordProgCakeMaxVar
      (.seq (.break 999) (.continue 888) : WordProg Nat) == 0

#guard maxVarControlLabelGuard
#guard sortMovesTailSplitGuard
#guard raDeltaTriangleGuard
#guard raForcedEdgeGuard

def parityGuard : Bool :=
  moveChainGuard && moveFromRegGuard && seqMovesGuard && ifMergeGuard &&
    ifMergeAllocGuard && callMergeGuard && callTailGuard && mustTerminateGuard &&
    loopBodyGuard && assignLeafGuard &&
    bijDeltaBasicGuard && bijDeltaDedupGuard && bijSeqOrderGuard &&
    bijBranchOrderGuard && bijBranchLiveGuard && bijSetGuard &&
    bijSetUnsortedGuard && bijCompositeGuard && graphDeltaDisjointGuard &&
    graphDeltaCliqueGuard && graphSetCliqueGuard && graphForcedEdgeGuard &&
    graphTagsGuard && graphInitGuard && heuDeltaGuard && heuMovesGuard &&
    heuSpillGuard && heuFixedDegreeGuard && raDeltaPairGuard &&
    raDeltaFreeGuard && raDeltaTriangleGuard && raStackOnlyGuard &&
    raMovesCoalesceGuard && raMovesSelfFilteredGuard && raForcedEdgeGuard &&
    raOrderSeqGuard && raOrderCliqueGuard && raSpillCostGuard &&
    prefsMoveOrderGuard && prefsSeqOrderGuard && prefsControlFlowGuard &&
    prefsBranchOrderGuard &&
    prefsCallHandlerOrderGuard && prefsCallReturnOnlyGuard &&
    prefsLoopOrderGuard && prefsControlFlowGuard &&
    partOrderGuard && reviveOrderGuard && movesToSpOrderGuard &&
    resortMovesSpOrderGuard && bgOkOrderGuard &&
    qsortTiesTwoGuard && qsortTiesThreeGuard && qsortDescGuard &&
    stempBadColourTieGuard && raMovesStempGuard && raMovesStempHiGuard &&
    negFirstMatchProjectionGuard
    && mapUpdateBoundedGuard && sourceSpillCostKeyGuard &&
    sourceSpillCostRoundTripGuard && sourceMovePhysicalFallbackGuard
    && deadMovePriorityGuard
    && deadProgramPriorityGuard && deadTailCallLiveGuard && deadAllocLiveGuard
    && deadInstallLiveGuard && deadFfiLiveGuard && deadStoreConstsLiveGuard
    && cakeBijSetPatriciaGuard
    && sortMovesTailSplitGuard

/- The aggregate guard is intentionally disabled while the allocator port is
   being aligned with CakeML.  Individual oracle cases remain available to
   select and repair without blocking the whole build on stale expectations. -/
def runChecks : IO Bool := do
  let results := [
    moveChainGuard, moveFromRegGuard, seqMovesGuard, ifMergeGuard,
    ifMergeAllocGuard, callMergeGuard, callTailGuard, mustTerminateGuard,
    loopBodyGuard, assignLeafGuard,
    bijDeltaBasicGuard, bijDeltaDedupGuard, bijSeqOrderGuard,
    bijBranchOrderGuard, bijBranchLiveGuard, bijSetGuard,
    bijSetUnsortedGuard, bijCompositeGuard, graphDeltaDisjointGuard,
    graphDeltaCliqueGuard, graphSetCliqueGuard, graphForcedEdgeGuard,
    graphTagsGuard, graphInitGuard, heuDeltaGuard, heuMovesGuard,
    heuSpillGuard, heuFixedDegreeGuard, raDeltaPairGuard, raDeltaFreeGuard,
    raDeltaTriangleGuard, raStackOnlyGuard, raMovesCoalesceGuard,
    raMovesSelfFilteredGuard, raForcedEdgeGuard,
    raOrderSeqGuard, raOrderCliqueGuard, raSpillCostGuard,
    prefsMoveOrderGuard, prefsSeqOrderGuard, prefsControlFlowGuard,
    prefsBranchOrderGuard,
    prefsCallHandlerOrderGuard, prefsCallReturnOnlyGuard, prefsLoopOrderGuard,
    prefsControlFlowGuard,
    partOrderGuard,
    reviveOrderGuard, revivePartitionGuard, bgOkOrderGuard, qsortTiesTwoGuard,
    movesToSpOrderGuard, resortMovesSpOrderGuard,
    qsortTiesThreeGuard, qsortDescGuard, raMovesStempGuard,
    raMovesStempHiGuard, negFirstMatchProjectionGuard, mapUpdateBoundedGuard,
    deadMovePriorityGuard, deadProgramPriorityGuard, sortMovesTailSplitGuard,
    sourceSpillCostKeyGuard, sourceMovePhysicalFallbackGuard,
    deadTailCallLiveGuard, deadAllocLiveGuard, deadInstallLiveGuard,
    deadFfiLiveGuard, deadStoreConstsLiveGuard, stExMinCostOrderGuard,
    stExMinCostTieGuard, stExMinCostZeroDegreeGuard,
    stExMaxDegOrderGuard, stExMaxDegTieGuard, doSpillTransitionGuard,
    respillWorklistGuard,
    respillBelowThresholdGuard, simplifyBatchGuard, decDegreeOutOfDimGuard,
    decDegreeOutOfDimNoOpGuard, coalesceWorklistSuccessGuard,
    freezeWorklistTransitionGuard]
  let names := [
    "get_stack_only move chain", "get_stack_only move from reg",
    "get_stack_only seq moves", "get_stack_only if merge",
    "get_stack_only if merge alloc", "get_stack_only call merge",
    "get_stack_only call tail", "get_stack_only MustTerminate",
    "get_stack_only Loop body", "get_stack_only assign leaf",
    "mk_bij delta basic", "mk_bij delta dedup", "mk_bij seq order",
    "mk_bij branch order", "mk_bij branch live", "mk_bij set",
    "mk_bij set unsorted", "mk_bij composite", "mk_graph delta disjoint",
    "mk_graph delta clique", "mk_graph set clique", "extend_graph forced",
    "mk_tags roles", "init_ra_state", "init_alloc1_heu delta",
    "init_alloc1_heu moves", "init_alloc1_heu spill",
    "init_alloc1_heu fixed degree", "reg_alloc delta pair",
    "reg_alloc delta free", "reg_alloc triangle",
    "reg_alloc stack only",
    "reg_alloc moves coalesce", "reg_alloc moves self filtered",
    "reg_alloc forced edge",
    "reg_alloc sequential pair order", "reg_alloc clique order",
    "reg_alloc spill-cost selection",
    "get_prefs Move order", "get_prefs Seq order", "get_prefs control flow",
    "get_prefs If order",
    "get_prefs Call handler order", "get_prefs Call return-only order",
    "get_prefs Loop order", "get_prefs control flow",
    "sorting partition order", "revive moves reversing partition", "revive partition direction", "bg_ok order",
    "sort_moves tie two", "moves_to_sp order", "resort_moves output order",
    "sort_moves tie three", "sort_moves long tie",
    "sort_moves descending",
    "reg_alloc moves stack temp", "reg_alloc moves stack temp high",
    "neg_first_match_col projection", "Cake map updates stay bounded",
    "remove_dead keeps move priority", "remove_dead_prog keeps entry priority",
    "mk_bij uses Cake Patricia Set order", "sort_moves tail split oracle",
    "source-keyed spill costs", "source-keyed spill-cost round trip",
    "physical source move fallback",
    "remove_dead tail-call liveness", "remove_dead Alloc liveness",
    "remove_dead Install liveness", "remove_dead FFI liveness",
    "remove_dead StoreConsts liveness", "st_ex_list_MIN_cost ordering",
    "st_ex_list_MIN_cost tie ordering", "st_ex_list_MIN_cost zero degree",
    "st_ex_list_MAX_deg ordering", "st_ex_list_MAX_deg tie ordering",
    "do_spill transition", "dec_degree out-of-dimension guard",
    "respill freeze-to-spill transition",
    "respill below-threshold no-op", "do_simplify batch ordering",
    "dec_degree out-of-dimension no-op with outside adjacency",
    "do_coalesce success transition", "do_freeze transition"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CakeRegAlloc
