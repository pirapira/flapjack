import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.SpillCosts
import Flapjack.CrepToLoop

/-!
# Cake register-allocation driver slice: stack-only analysis

This module ports the allocator-driver pieces of CakeML's `word_alloc`
(`cakeml/compiler/backend/word_allocScript.sml`) that decide which
variables must live in stack slots before graph colouring runs:

* `cakeGetStackOnlyAux` / `cakeGetStackOnly`
  (`get_stack_only_aux` / `get_stack_only`,
  `word_allocScript.sml:1741-1789`): the variables that are already stack
  variables or only ever involved in stack moves, computed from the move
  graph and the clash tree.  These are the frame-relevant "forced stack"
  inputs consumed by the IRC allocator.

It is the driver-side slice for bead `flapjack-pxn.8.5.14.1.3` (frame
occupancy and allocator temporary slots) and builds on the core primitives
in `Flapjack.RiscV.CakeAlloc` (bead `.1.3.1`).
-/

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack.RiscV.CakeAlloc (mergeStackOnly mergeStackSets removeTempStack
  getForcedAddCarry getForcedLongMul)

/-! RISC-V exposes 32 hardware registers, with five avoided by Cake's
    backend configuration (`0, 2, 3, 4, 31`).  `word_alloc` therefore colours
    against 22 usable registers, not the raw Word-name pool size. -/
def cakeRiscVRegisterCount : Nat := 32 - (5 + 5)

/-- `get_stack_only_aux` (`word_allocScript.sml:1741-1789`).

    Threads the temporary/forced-stack pair `(ts, fs)` backwards through
    the program.  Moves propagate the stack-only decision, sequences
    process the second half first, branches merge, calls merge the
    return-handler and exception-handler analyses, and every other
    statement consults the clash tree: a `Delta` node removes its written
    and read names from the temporaries set. -/
def cakeGetStackOnlyAux {α : Type u} :
    List Nat × List Nat → WordProg α → List Nat × List Nat
  | tfs, .move _ moves =>
      moves.foldr (fun move acc => mergeStackOnly move.1 move.2 acc.1 acc.2) tfs
  | tfs, .seq first second => cakeGetStackOnlyAux (cakeGetStackOnlyAux tfs second) first
  | tfs, .ite _ condition right thenBranch elseBranch =>
      let left := cakeGetStackOnlyAux tfs thenBranch
      let rightTfs := cakeGetStackOnlyAux tfs elseBranch
      let merged := mergeStackSets tfs.1 tfs.2 left.1 left.2 rightTfs.1 rightTfs.2
      match right with
      | .reg name => removeTempStack [condition, name] merged.1 merged.2
      | _ => removeTempStack [condition] merged.1 merged.2
  | tfs, .mustTerminate body => cakeGetStackOnlyAux tfs body
  | tfs, .call (some (_, _, returnHandler, _, _)) _ _ handler =>
      let returnTfs := cakeGetStackOnlyAux tfs returnHandler
      match handler with
      | none => returnTfs
      | some (_, handlerBody, _, _) =>
          let handlerTfs := cakeGetStackOnlyAux tfs handlerBody
          mergeStackSets tfs.1 tfs.2 returnTfs.1 returnTfs.2 handlerTfs.1 handlerTfs.2
  | tfs, .call none _ _ _ => tfs
  | tfs, .loop _ body _ => cakeGetStackOnlyAux tfs body
  | tfs, program =>
      match wordClashTree program [] with
      | .delta writes reads => removeTempStack (writes ++ reads) tfs.1 tfs.2
      | _ => tfs
  termination_by _tfs program => sizeOf program
  decreasing_by
    all_goals first
      | sizeOf_list_dec | decreasing_tactic | decreasing_trivial
        <;> simp_arith

/-- `get_stack_only` (`word_allocScript.sml:1787-1789`): the forced-stack
    variable list for a whole program. -/
def cakeGetStackOnly {α : Type u} (program : WordProg α) : List Nat :=
  (cakeGetStackOnlyAux ([], []) program).2

/-! RISC-V `get_forced` traversal.  The source adds hardware interference
    edges for the carry and long-multiply instructions, then walks sequence,
    branch, call-handler, and loop bodies in reverse continuation order. -/
def cakeForcedArith : WordArith → List (Nat × Nat)
  | .addCarry destination _ sourceLeft sourceRight _ =>
      getForcedAddCarry destination sourceLeft sourceRight
  | .cakeAddCarry destination sourceLeft sourceRight _ =>
      getForcedAddCarry destination sourceLeft sourceRight
  | .longMul destinationLeft _ sourceLeft sourceRight =>
      getForcedLongMul destinationLeft sourceLeft sourceRight
  | _ => []

def cakeGetForcedAux {α : Type u} :
    WordProg α → List (Nat × Nat) → List (Nat × Nat)
  | .inst (.arith operation), forced => cakeForcedArith operation ++ forced
  | .mustTerminate body, forced => cakeGetForcedAux body forced
  | .seq first second, forced =>
      cakeGetForcedAux first (cakeGetForcedAux second forced)
  | .ite _ _ _ thenBranch elseBranch, forced =>
      cakeGetForcedAux thenBranch (cakeGetForcedAux elseBranch forced)
  | .call (some (_, _, returnHandler, _, _)) _ _ handler, forced =>
      let forced := cakeGetForcedAux returnHandler forced
      match handler with
      | none => forced
      | some (_, handlerBody, _, _) => cakeGetForcedAux handlerBody forced
  | .loop _ body _, forced => cakeGetForcedAux body forced
  | _, forced => forced
  termination_by _program => sizeOf _program
  decreasing_by
    all_goals first
      | decreasing_tactic | decreasing_trivial

def cakeGetForced {α : Type u} (program : WordProg α) : List (Nat × Nat) :=
  cakeGetForcedAux program []

/-! ## Clash-tree to allocator-node bijection

`mk_bij` / `list_remap` / `mk_bij_aux`
(`cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1096-1130`) map the
variables of a clash tree onto dense allocator node numbers `0, 1, ...` in
first-appearance order.  Inside a `Delta` node the reads list is remapped
before the writes list, a `Seq` node remaps its right subtree first, a
`Branch` node remaps the left subtree, then the right subtree, then the
optional live set, and a `Set` node remaps its fixed list in ascending
order (the original enumerates a `num_set` via `toAList`, which is always
ascending; Flapjack's clash tree stores a plain list, so the port sorts
it at this boundary to keep the numbering faithful). -/

/-- The bijection computed by `mk_bij`: variable-to-node and node-to-variable
    maps plus the next fresh node number. -/
structure CakeNodeBijection where
  toAllocator : NatInfoMap Nat
  fromAllocator : NatInfoMap Nat
  nextNode : Nat
  deriving Repr

/-- `list_remap` (`reg_allocScript.sml:1096-1103`): assign fresh allocator
    node numbers to the not-yet-mapped names of a list, left to right. -/
def cakeListRemap : List Nat → CakeNodeBijection → CakeNodeBijection
  | [], bijection => bijection
  | name :: names, bijection =>
      match lookupNatInfo name bijection.toAllocator with
      | some _ => cakeListRemap names bijection
      | none =>
          cakeListRemap names
            { toAllocator := (name, bijection.nextNode) :: bijection.toAllocator
              fromAllocator := (bijection.nextNode, name) :: bijection.fromAllocator
              nextNode := bijection.nextNode + 1 }

/-- `mk_bij_aux` (`reg_allocScript.sml:1105-1117`).  The `Set` case sorts
    its names first: the original walks `MAP FST (toAList t)` over a
    `num_set`, which enumerates keys in ascending order, while Flapjack's
    clash tree carries the names as an arbitrary-order list (call sites use
    `eraseDups` first-appearance order); sorting here keeps the node
    numbering faithful regardless of caller order. -/
def cakeMkBijAux : WordClashTree → CakeNodeBijection → CakeNodeBijection
  | .delta writes reads, bijection =>
      cakeListRemap writes (cakeListRemap reads bijection)
  | .set names, bijection =>
      cakeListRemap (names.mergeSort (fun a b => a < b)) bijection
  | .branch live thenBranch elseBranch, bijection =>
      let mapped := cakeMkBijAux elseBranch (cakeMkBijAux thenBranch bijection)
      match live with
      | none => mapped
      | some names =>
          cakeListRemap (names.mergeSort (fun a b => a < b)) mapped
  | .seq first second, bijection => cakeMkBijAux first (cakeMkBijAux second bijection)

/-- `mk_bij` (`reg_allocScript.sml:1119-1127`): the node bijection for a
    whole clash tree, starting from the empty bijection at node zero. -/
def cakeMkBij (tree : WordClashTree) : CakeNodeBijection :=
  cakeMkBijAux tree { toAllocator := [], fromAllocator := [], nextNode := 0 }

end Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.RiscV.CakeRegAlloc

/-! ## IRC allocator state: graph construction

The pieces of CakeML's IRC allocator state setup
(`cakeml/compiler/backend/reg_alloc/reg_allocScript.sml`) that turn a clash
tree, a forced-edge list, and the stack-only set into the initial allocator
state: the node adjacency lists and the node tags.  The mutable array state
of the original is represented functionally as `NatInfoMap`s with
newest-wins update.  Internal allocator state is not directly observable
through HOL evaluation (the original threads it through a state monad over
arrays), so this slice is guarded by structural checks derived from the
definitions; the end-to-end colouring oracles
(`scripts/hol-probes/reg_alloc_probe.out`) validate the whole machine once
the remaining worklist slices land. -/

/-- Node tags (`node_tag` in the original state record). -/
inductive CakeNodeTag
  | aTemp | sTemp | fixed (register : Nat)
  deriving Repr, BEq

/-- The IRC allocator state (`ra_state`), represented functionally. -/
structure CakeRaState where
  adjLists : NatInfoMap (List Nat)
  nodeTag : NatInfoMap CakeNodeTag
  degrees : NatInfoMap Nat
  coalesced : NatInfoMap Nat
  moveRelated : NatInfoMap Bool
  dim : Nat
  simpWl : List Nat
  spillWl : List Nat
  freezeWl : List Nat
  availMovesWl : List (Nat × (Nat × Nat))
  unavailMovesWl : List (Nat × (Nat × Nat))
  stack : List Nat
  deriving Repr

/-- The empty allocator state for `n` nodes. -/
def CakeRaState.empty (n : Nat) : CakeRaState :=
  { adjLists := [], nodeTag := [], degrees := [], coalesced := [],
    moveRelated := [], dim := n, simpWl := [], spillWl := [], freezeWl := [],
    availMovesWl := [], unavailMovesWl := [], stack := [] }

/- CakeML's allocator stores these fields in fixed-size arrays and every
   `update_*` accessor performs an in-place `LUPDATE`.  The association-list
   representation keeps the same newest-wins lookup convention, but must
   replace the first binding for an existing key rather than consing a new
   historical binding on every state transition.  Appending a missing key is
   only a representation fallback: well-formed allocator fields are
   dimensioned for every node, so the normal path remains bounded. -/
def cakeMapUpdate {α : Type u} (m : NatInfoMap α) (i : Nat) (v : α) : NatInfoMap α :=
  match m with
  | [] => [(i, v)]
  | (j, w) :: entries =>
      if i == j then (i, v) :: entries
      else (j, w) :: cakeMapUpdate entries i v

/-- First-match lookup in a `NatInfoMap` (newest binding wins). -/
def cakeMapLookup {α : Type u} (m : NatInfoMap α) (i : Nat) : Option α :=
  Flapjack.lookupNatInfo i m

/-- `sorted_insert` (`reg_allocScript.sml:184-189`): insert into a
    descending adjacency list, skipping duplicates. -/
def cakeSortedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x = y then y :: ys
      else if x > y then x :: y :: ys
      else y :: cakeSortedInsert x ys

/-- Adjacency list of node `i` (`adj_ls_sub`). -/
def cakeAdjSub (adj : NatInfoMap (List Nat)) (i : Nat) : List Nat :=
  (cakeMapLookup adj i).getD []

/-- `insert_edge` (`reg_allocScript.sml:201-212`): undirected edge into the
    adjacency representation. -/
def cakeInsertEdge (x y : Nat) (adj : NatInfoMap (List Nat)) :
    NatInfoMap (List Nat) :=
  let adjX := cakeMapUpdate adj x (cakeSortedInsert y (cakeAdjSub adj x))
  cakeMapUpdate adjX y (cakeSortedInsert x (cakeAdjSub adj y))

/-- `list_insert_edge` (`reg_allocScript.sml:214-221`). -/
def cakeListInsertEdge (x : Nat) : List Nat → NatInfoMap (List Nat) →
    NatInfoMap (List Nat)
  | [], adj => adj
  | y :: ys, adj => cakeListInsertEdge x ys (cakeInsertEdge x y adj)

/-- `clique_insert_edge` (`reg_allocScript.sml:223-232`). -/
def cakeCliqueInsertEdge : List Nat → NatInfoMap (List Nat) →
    NatInfoMap (List Nat)
  | [], adj => adj
  | x :: xs, adj => cakeCliqueInsertEdge xs (cakeListInsertEdge x xs adj)

/-- `extend_clique` (`reg_allocScript.sml:235-249`): extend an existing
    clique with new members, returning the extended live list. -/
def cakeExtendClique : List Nat → List Nat → NatInfoMap (List Nat) →
    NatInfoMap (List Nat) × List Nat
  | [], cli, adj => (adj, cli)
  | x :: xs, cli, adj =>
      if cli.contains x then cakeExtendClique xs cli adj
      else cakeExtendClique xs (x :: cli) (cakeListInsertEdge x cli adj)
termination_by new _ _ => sizeOf new
decreasing_by all_goals decreasing_trivial

/-- `mk_graph` (`reg_allocScript.sml:1179-1218`): build the adjacency
    representation from a clash tree, threading the live list.  `ta` maps
    original variable names to node ids (`sp_default` over the bijection).
    The `Set` case walks the original sptree keys in ascending order, so the
    fixed clash-tree set is sorted at this boundary like in `cakeMkBijAux`. -/
def cakeMkGraph (ta : Nat → Nat) : WordClashTree → List Nat →
    NatInfoMap (List Nat) → NatInfoMap (List Nat) × List Nat
  | .delta writes reads, liveout, adj =>
      let wta := writes.map ta
      let rta := reads.map ta
      let (adj1, live) := cakeExtendClique wta liveout adj
      cakeExtendClique rta (live.filter (fun x => !wta.contains x)) adj1
  | .set names, _liveout, adj =>
      let live := (names.mergeSort (fun a b => a < b)).map ta
      (cakeCliqueInsertEdge live adj, live)
  | .branch topt t1 t2, liveout, adj =>
      let (adj1, t1Live) := cakeMkGraph ta t1 liveout adj
      let (adj2, t2Live) := cakeMkGraph ta t2 liveout adj1
      match topt with
      | none => cakeExtendClique t1Live t2Live adj2
      | some t =>
          let live := (t.mergeSort (fun a b => a < b)).map ta
          (cakeCliqueInsertEdge live adj2, live)
  | .seq t1 t2, liveout, adj =>
      let (adj1, live) := cakeMkGraph ta t2 liveout adj
      cakeMkGraph ta t1 live adj1
termination_by tree _ _ => sizeOf tree
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `extend_graph` (`reg_allocScript.sml:1224-1230`): add the forced edges. -/
def cakeExtendGraph (ta : Nat → Nat) : List (Nat × Nat) →
    NatInfoMap (List Nat) → NatInfoMap (List Nat)
  | [], adj => adj
  | (x, y) :: rest, adj =>
      cakeExtendGraph ta rest (cakeInsertEdge (ta x) (ta y) adj)

/-- `mk_tags` (`reg_allocScript.sml:1159-1176`): tag every node with its
    original variable's role.  Stack-only variables (from `get_stack_only`,
    keyed by original variable name) become `Stemp`, other allocatable
    variables `Atemp`, and physical variables `Fixed` of their register.  The
    original looks up `fa` through `sp_default`, so an unmapped node falls
    back to variable `0`, i.e. `Fixed 0`. -/
def cakeMkTags (n : Nat) (fromAllocator : NatInfoMap Nat) (fs : List Nat) :
    NatInfoMap CakeNodeTag :=
  (List.range n).foldl (fun tags i =>
      let v := CakeAlloc.spDefault fromAllocator i
      match v % 4 with
      | 1 => cakeMapUpdate tags i (if fs.contains v then .sTemp else .aTemp)
      | 3 => cakeMapUpdate tags i .sTemp
      | _ => cakeMapUpdate tags i (.fixed (v / 2)))
    []

/-- `init_ra_state` (`reg_allocScript.sml:1241-1250`): the initial allocator
    state for a clash tree. -/
def cakeInitRaState (tree : WordClashTree) (forced : List (Nat × Nat))
    (fs : List Nat) : CakeRaState :=
  let bij := cakeMkBij tree
  let ta := CakeAlloc.spDefault bij.toAllocator
  let (adj, _) := cakeMkGraph ta tree [] []
  let adj := cakeExtendGraph ta forced adj
  let tags := cakeMkTags bij.nextNode bij.fromAllocator fs
  { (CakeRaState.empty bij.nextNode) with
    adjLists := adj, nodeTag := tags }

/-- `is_Fixed` (`reg_allocScript.sml:449-454`): a physical node. -/
def cakeIsFixed (state : CakeRaState) (x : Nat) : Bool :=
  match (cakeMapLookup state.nodeTag x).getD .aTemp with
  | .fixed _ => true
  | _ => false

/-- `is_Fixed_k` (`reg_allocScript.sml:501-506`): a physical node within the
    allocatable window `k`. -/
def cakeIsFixedK (state : CakeRaState) (k : Nat) (x : Nat) : Bool :=
  match (cakeMapLookup state.nodeTag x).getD .aTemp with
  | .fixed n => n < k
  | _ => false

/-- `considered_var` (`reg_allocScript.sml:507-512`): allocation temps and
    low physical registers count towards degrees. -/
def cakeConsideredVar (state : CakeRaState) (k : Nat) (v : Nat) : Bool :=
  ((cakeMapLookup state.nodeTag v).getD .aTemp == .aTemp) || cakeIsFixedK state k v

/-- `is_not_coalesced` (`reg_allocScript.sml:320-327`): the node is its own
    coalescing parent. -/
def cakeIsNotCoalesced (state : CakeRaState) (v : Nat) : Bool :=
  (cakeMapLookup state.coalesced v).getD v == v

/-- `split_degree` (`reg_allocScript.sml:330-340`): low-degree (relative to
    `k`) uncoalesced allocation nodes; nodes at or above the dimension stay
    on the worklist side. -/
def cakeSplitDegree (state : CakeRaState) (d k v : Nat) : Bool :=
  if v < d then
    ((cakeMapLookup state.degrees v).getD 0 < k) && cakeIsNotCoalesced state v
  else true

/-- `st_ex_filter`/`st_ex_partition` accumulate by prepending, so the
    results are reversed (`reg_allocScript.sml:158-180`). -/
def filterReversed {α : Type u} (p : α → Bool) (l : List α) : List α :=
  (l.filter p).reverse

def partitionReversed {α : Type u} (p : α → Bool) (l : List α) : List α × List α :=
  let (tt, ff) := l.partition p
  (tt.reverse, ff.reverse)

/-- `QSORT` (`sortingScript.sml:747-752`) as observed on the original's
    `sort_moves` outputs: an element goes to the left bucket when it does
    not sort strictly after the pivot, and the partition buckets are
    prepended and therefore reversed.  The fuel is the input length, which
    bounds the recursion depth because each partition is strictly shorter
    than its input. -/
def cakeQSortAux {α : Type u} (ord : α → α → Bool) : Nat → List α → List α
  | _, [] => []
  | fuel + 1, h :: t =>
      let (l1, l2) := partitionReversed (fun y => ord y h) t
      cakeQSortAux ord fuel l1 ++ [h] ++ cakeQSortAux ord fuel l2
  | 0, _ :: _ => []

def cakeQSort {α : Type u} (ord : α → α → Bool) (moves : List α) : List α :=
  cakeQSortAux ord (moves.length + 1) moves

/-- `sort_moves` (`reg_allocScript.sml:343-346`): the original sorts with
    `QSORT`; probed on the original, an equal-priority move lands before the
    pivot and the partition buckets reverse, so equal priorities flip
    relative to the input order (probes `sort_moves_probe.out`
    `sm_ties_two`/`sm_ties_three`). -/
def cakeSortMoves (moves : List (Nat × (Nat × Nat))) :
    List (Nat × (Nat × Nat)) :=
  cakeQSort (fun a b => a.1 >= b.1) moves

/-- `move_related_sub`: a node flagged by `reset_move_related`. -/
def cakeMoveRelatedSub (state : CakeRaState) (v : Nat) : Bool :=
  (cakeMapLookup state.moveRelated v).getD false

/-- `init_alloc1_heu` (`reg_allocScript.sml:1262-1286`): degrees count only
    considered neighbours, every node becomes its own coalescing parent, the
    move worklist is sorted by priority, `reset_move_related`
    (`:708-725`) clears the flags and re-marks non-fixed move endpoints, and
    the allocation temps split into spill / freeze / simplify worklists. -/
def cakeInitAlloc1Heu (moves : List (Nat × (Nat × Nat))) (k : Nat)
    (state : CakeRaState) : Nat × CakeRaState :=
  let dim := state.dim
  let ds := List.range dim
  let allocs := filterReversed (fun i =>
    (cakeMapLookup state.nodeTag i).getD .aTemp == .aTemp) ds
  let withDegrees :=
    ds.foldl (fun st i =>
        let neighbours := (cakeMapLookup st.adjLists i).getD []
        let fills := neighbours.filter (cakeConsideredVar st k)
        { st with degrees := cakeMapUpdate st.degrees i fills.length })
      state
  let withCoalesced :=
    ds.foldl (fun st i =>
        { st with coalesced := cakeMapUpdate st.coalesced i (0 + i) })
      withDegrees
  let withMoves :=
    { withCoalesced with
      availMovesWl := cakeSortMoves moves }
  let cleared :=
    ds.foldl (fun st i =>
        { st with moveRelated := cakeMapUpdate st.moveRelated i false })
      withMoves
  let withRelated :=
    moves.foldl (fun st move =>
        let x := move.2.1
        let y := move.2.2
        let fixedX := cakeIsFixed st x
        let fixedY := cakeIsFixed st y
        let st := { st with moveRelated := cakeMapUpdate st.moveRelated x (!fixedX) }
        { st with moveRelated := cakeMapUpdate st.moveRelated y (!fixedY) })
      cleared
  let (ltk, gtk) := partitionReversed (fun v => cakeSplitDegree withRelated dim k v) allocs
  let (ltkfreeze, ltksimp) := partitionReversed (fun v => cakeMoveRelatedSub withRelated v) ltk
  let final :=
    { withRelated with
      spillWl := gtk, simpWl := ltksimp, freezeWl := ltkfreeze }
  (allocs.length, final)

/-! ### The IRC worklist machine (`reg_allocScript.sml:251-868`)

The original runs these transitions in a state monad over growable
arrays; this port threads `CakeRaState` functionally. -/

/-- `dec_deg` (`reg_allocScript.sml:256-272`): decrement one adjacent
    node's degree. -/
def cakeDecDeg (v : Nat) (state : CakeRaState) : CakeRaState :=
  let d := (cakeMapLookup state.degrees v).getD 0
  { state with degrees := cakeMapUpdate state.degrees v (d - 1) }

/-- `dec_degree`: decrement the degrees of all nodes adjacent to `x`. -/
def cakeDecDegree (x : Nat) (state : CakeRaState) : CakeRaState :=
  (cakeAdjSub state.adjLists x).foldl (fun s v => cakeDecDeg v s) state

/-- `push_stack` (`reg_allocScript.sml:300-307`). -/
def cakePushStack (x : Nat) (state : CakeRaState) : CakeRaState :=
  { state with
    degrees := cakeMapUpdate state.degrees x 0,
    moveRelated := cakeMapUpdate state.moveRelated x false,
    stack := x :: state.stack }

/-- `add_simp_wl` / `add_spill_wl` / `add_freeze_wl`. -/
def cakeAddSimpWl (ls : List Nat) (state : CakeRaState) : CakeRaState :=
  { state with simpWl := ls ++ state.simpWl }

def cakeAddSpillWl (ls : List Nat) (state : CakeRaState) : CakeRaState :=
  { state with spillWl := ls ++ state.spillWl }

def cakeAddFreezeWl (ls : List Nat) (state : CakeRaState) : CakeRaState :=
  { state with freezeWl := ls ++ state.freezeWl }

/-- `add_unavail_moves_wl` (`reg_allocScript.sml:309-313`). -/
def cakeAddUnavailMovesWl (ls : List (Nat × (Nat × Nat)))
    (state : CakeRaState) : CakeRaState :=
  { state with unavailMovesWl := ls ++ state.unavailMovesWl }

/-- `smerge` (`reg_allocScript.sml:349-358`): stable merge of two
    descending priority-sorted move lists; ties take the left list. -/
def cakeSMerge : List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat)) →
    List (Nat × (Nat × Nat))
  | [], ms => ms
  | ms, [] => ms
  | (p1, m1) :: ms1, (p2, m2) :: ms2 =>
      if p1 >= p2 then (p1, m1) :: cakeSMerge ms1 ((p2, m2) :: ms2)
      else (p2, m2) :: cakeSMerge ((p1, m1) :: ms1) ms2
termination_by ms1 ms2 => sizeOf ms1 + sizeOf ms2
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `revive_moves` (`reg_allocScript.sml:363-375`). -/
def cakeReviveMoves (vs : List Nat) (state : CakeRaState) : CakeRaState :=
  let nbs := vs.map (fun v => cakeAdjSub state.adjLists v)
  let (revived, unavail) := partitionReversed (fun m =>
      nbs.any (fun nb => nb.contains m.2.1 || nb.contains m.2.2))
    state.unavailMovesWl
  { state with
    availMovesWl := cakeSMerge (cakeSortMoves revived) state.availMovesWl,
    unavailMovesWl := unavail }

/-- `unspill` (`reg_allocScript.sml:378-391`). -/
def cakeUnspill (k : Nat) (state : CakeRaState) : CakeRaState :=
  let (ltk, gtk) := partitionReversed (fun v => cakeSplitDegree state state.dim k v) state.spillWl
  let state := cakeReviveMoves ltk state
  let (freeze, simp) := partitionReversed (fun v => cakeMoveRelatedSub state v) ltk
  let state := { state with spillWl := gtk }
  let state := cakeAddSimpWl simp state
  cakeAddFreezeWl freeze state

/-- `do_simplify` (`reg_allocScript.sml:400-421`). -/
def cakeDoSimplify (k : Nat) (state : CakeRaState) : Bool × CakeRaState :=
  match state.simpWl with
  | [] => (false, state)
  | _ =>
      let state := state.simpWl.foldl (fun s x => cakeDecDegree x s) state
      let state := state.simpWl.foldl (fun s x => cakePushStack x s) state
      (true, cakeUnspill k { state with simpWl := [] })

/-- `inc_deg` (`reg_allocScript.sml:424-429`). -/
def cakeIncDeg (n d : Nat) (state : CakeRaState) : CakeRaState :=
  let old := (cakeMapLookup state.degrees n).getD 0
  { state with degrees := cakeMapUpdate state.degrees n (old + d) }

/-- `deg_or_inf` (`reg_allocScript.sml:524-531`). -/
def cakeDegOrInf (state : CakeRaState) (k x : Nat) : Nat :=
  if cakeIsFixedK state k x then k else (cakeMapLookup state.degrees x).getD 0

/-- `bg_ok` (`reg_allocScript.sml:533-562`): the George coalescing test,
    returning the (case1, case2) adjacency splits on success. -/
def cakeBgOk (k x y : Nat) (state : CakeRaState) : Option (List Nat × List Nat) :=
  let adjX := cakeAdjSub state.adjLists x
  let adjY := cakeAdjSub state.adjLists y
  let (case1, case2) := partitionReversed (fun v => adjX.contains v) adjY
  let case1 := filterReversed (fun v => cakeConsideredVar state k v) case1
  let case2 := filterReversed (fun v => cakeConsideredVar state k v) case2
  let case2degs := case2.map (fun v => cakeDegOrInf state k v)
  if !case2degs.any (fun d => d >= k) then
    some (case1, case2)
  else
    let case3 := filterReversed (fun v => cakeConsideredVar state k v)
      (adjX.filter (fun v => !adjY.contains v))
    let c1 := (case1.map (fun v => cakeDegOrInf state (k + 1) v)).countP
      (fun d => d - 1 >= k)
    let c2 := case2degs.countP (fun d => d >= k)
    let c3 := (case3.map (fun v => cakeDegOrInf state k v)).countP
      (fun d => d >= k)
    if c1 + c2 + c3 < k then some (case1, case2) else none

/-- `consistency_ok` (`reg_allocScript.sml:568-586`). -/
def cakeConsistencyOk (state : CakeRaState) (x y : Nat) : Bool :=
  x != y && !(cakeAdjSub state.adjLists y).contains x &&
    (cakeIsFixed state x || (cakeMapLookup state.moveRelated x).getD false) &&
    (cakeIsFixed state y || (cakeMapLookup state.moveRelated y).getD false) &&
    !(cakeIsFixed state x && cakeIsFixed state y)

/-- `do_coalesce_real` (`reg_allocScript.sml:458-471`). -/
def cakeDoCoalesceReal (x y : Nat) (case1 case2 : List Nat)
    (state : CakeRaState) : CakeRaState :=
  let state := { state with coalesced := cakeMapUpdate state.coalesced y x }
  let state := if !cakeIsFixed state x then
    cakeIncDeg x case2.length state else state
  let state := { state with
    adjLists := cakeListInsertEdge x case2 state.adjLists }
  let state := case1.foldl (fun s v => cakeDecDeg v s) state
  cakePushStack y state

/-- `coalesce_parent` (`reg_allocScript.sml:592-612`) with path
    compression. -/
def cakeCoalesceParent : Nat → CakeRaState → Nat × CakeRaState
  | x, state =>
      let xt := (cakeMapLookup state.coalesced x).getD x
      if cakeIsFixed state xt then (xt, state)
      else if _h : x <= xt then (x, state)
      else
        let (anc, state) := cakeCoalesceParent xt state
        (anc, { state with coalesced := cakeMapUpdate state.coalesced x anc })
termination_by x _ => x
decreasing_by all_goals omega

/-- `canonize_move` (`reg_allocScript.sml:614-624`). -/
def cakeCanonizeMove (state : CakeRaState) (x y : Nat) : Nat × Nat :=
  if cakeIsFixed state y then (y, x)
  else if cakeIsFixed state x then (x, y)
  else if x < y then (x, y) else (y, x)

/-- `st_ex_FIRST` (`reg_allocScript.sml:636-657`): scan the available
    moves for the first passing both predicates; rejected moves are dropped
    or canonicalized into the unavailable list. -/
def cakeStExFirst (P : CakeRaState → Nat → Nat → Bool)
    (Q : CakeRaState → Nat → Nat → Option (List Nat × List Nat)) :
    CakeRaState → List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat)) →
    (Option ((Nat × Nat) × (List Nat × List Nat) × List (Nat × (Nat × Nat))) ×
      List (Nat × (Nat × Nat)) × CakeRaState)
  | state, [], unavail => (none, unavail, state)
  | state, (p, (u, v)) :: ms, unavail =>
      let (x, state) := cakeCoalesceParent u state
      let (y, state) := cakeCoalesceParent v state
      if !P state x y then cakeStExFirst P Q state ms unavail
      else
        let (cx, cy) := cakeCanonizeMove state x y
        match Q state cx cy with
        | none => cakeStExFirst P Q state ms ((p, (cx, cy)) :: unavail)
        | some pr => (some ((cx, cy), pr, ms), unavail, state)
termination_by _ ms _ => sizeOf ms
decreasing_by all_goals decreasing_trivial

/-- `respill` (`reg_allocScript.sml:659-674`). -/
def cakeRespill (k x : Nat) (state : CakeRaState) : CakeRaState :=
  if (cakeMapLookup state.degrees x).getD 0 < k then state
  else if state.freezeWl.contains x then
    let state := cakeAddSpillWl [x] state
    { state with freezeWl := state.freezeWl.filter (· ≠ x) }
  else state

/-- `do_coalesce` (`reg_allocScript.sml:676-698`). -/
def cakeDoCoalesce (k : Nat) (state : CakeRaState) : Bool × CakeRaState :=
  let (ores, unavail, state) :=
    cakeStExFirst cakeConsistencyOk (fun s x y => cakeBgOk k x y s)
      state state.availMovesWl []
  let state := cakeAddUnavailMovesWl unavail state
  match ores with
  | none => (false, { state with availMovesWl := [] })
  | some ((x, y), (case1, case2), ms) =>
      let state := cakeDoCoalesceReal x y case1 case2
        { state with availMovesWl := ms }
      let state := cakeUnspill k state
      (true, cakeRespill k x state)

/-- `reset_move_related` (`reg_allocScript.sml:708-725`). -/
def cakeResetMoveRelated (moves : List (Nat × (Nat × Nat)))
    (state : CakeRaState) : CakeRaState :=
  let cleared := (List.range state.dim).foldl (fun m v =>
    cakeMapUpdate m v false) state.moveRelated
  let updated := moves.foldl (fun m move =>
      let mx := !cakeIsFixed state move.2.1
      let my := !cakeIsFixed state move.2.2
      cakeMapUpdate (cakeMapUpdate m move.2.1 mx) move.2.2 my)
    cleared
  { state with moveRelated := updated }

/-- `do_prefreeze` (`reg_allocScript.sml:727-747`). -/
def cakeDoPrefreeze (k : Nat) (state : CakeRaState) : Bool × CakeRaState :=
  let fwl := filterReversed (fun x => cakeIsNotCoalesced state x) state.freezeWl
  let state := { state with
    spillWl := filterReversed (fun x => cakeIsNotCoalesced state x) state.spillWl }
  let uam := filterReversed
    (fun m => cakeConsistencyOk state m.2.1 m.2.2) state.unavailMovesWl
  let state := cakeResetMoveRelated uam state
  let state := { state with unavailMovesWl := uam }
  let (freeze, simp) := partitionReversed (fun v => cakeMoveRelatedSub state v) fwl
  let state := cakeAddSimpWl simp state
  let state := { state with freezeWl := freeze }
  cakeDoSimplify k state

/-- `do_freeze` (`reg_allocScript.sml:749-764`). -/
def cakeDoFreeze (k : Nat) (state : CakeRaState) : Bool × CakeRaState :=
  match state.freezeWl with
  | [] => (false, state)
  | x :: xs =>
      let state := cakePushStack x (cakeDecDegree x state)
      (true, cakeUnspill k { state with freezeWl := xs })

/-- `safe_div` (`reg_allocScript.sml:771`). -/
def cakeSafeDiv (x v : Nat) : Nat := if v = 0 then 0 else x / v

/-- `st_ex_list_MIN_cost` (`reg_allocScript.sml:773-790`). -/
def cakeStExListMinCost (degrees : NatInfoMap Nat) (scost : NatInfoMap Nat) :
    List Nat → Nat → Nat → Nat → List Nat → Nat × List Nat
  | [], _, k, _, acc => (k, acc)
  | x :: xs, d, k, v, acc =>
      if x < d then
        let xv := (cakeMapLookup degrees x).getD 0
        let cost := cakeSafeDiv ((cakeMapLookup scost x).getD 0) xv
        if v > cost then
          cakeStExListMinCost degrees scost xs d x cost (k :: acc)
        else cakeStExListMinCost degrees scost xs d k v (x :: acc)
      else cakeStExListMinCost degrees scost xs d k v acc
termination_by l _ _ _ _ => sizeOf l
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `st_ex_list_MAX_deg` (`reg_allocScript.sml:792-808`). -/
def cakeStExListMaxDeg (degrees : NatInfoMap Nat) :
    List Nat → Nat → Nat → Nat → List Nat → Nat × List Nat
  | [], _, k, _, acc => (k, acc)
  | x :: xs, d, k, v, acc =>
      if x < d then
        let xv := (cakeMapLookup degrees x).getD 0
        if v < xv then cakeStExListMaxDeg degrees xs d x xv (k :: acc)
        else cakeStExListMaxDeg degrees xs d k v (x :: acc)
      else cakeStExListMaxDeg degrees xs d k v acc
termination_by l _ _ _ _ => sizeOf l
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `do_spill` (`reg_allocScript.sml:810-830`). -/
def cakeDoSpill (scost : Option (NatInfoMap Nat)) (k : Nat)
    (state : CakeRaState) : Bool × CakeRaState :=
  match state.spillWl with
  | [] => (false, state)
  | x :: xs =>
      let xv := (cakeMapLookup state.degrees x).getD 0
      let (y, ys) := match scost with
        | none => cakeStExListMaxDeg state.degrees xs state.dim x xv []
        | some sc =>
            cakeStExListMinCost state.degrees sc xs state.dim x
              (cakeSafeDiv ((cakeMapLookup sc x).getD 0) xv) []
      let state := cakePushStack y (cakeDecDegree y state)
      (true, cakeUnspill k { state with spillWl := ys })

/-- `do_step` (`reg_allocScript.sml:832-857`): the first successful
    transition wins. -/
def cakeDoStep (scost : Option (NatInfoMap Nat)) (k : Nat)
    (state : CakeRaState) : Bool × CakeRaState :=
  let (b1, s1) := cakeDoSimplify k state
  if b1 then (true, s1)
  else
    let (b2, s2) := cakeDoCoalesce k state
    if b2 then (true, s2)
    else
      let (b3, s3) := cakeDoPrefreeze k state
      if b3 then (true, s3)
      else
        let (b4, s4) := cakeDoFreeze k state
        if b4 then (true, s4) else cakeDoSpill scost k state

/-- `rpt_do_step` (`reg_allocScript.sml:860-868`). -/
def cakeRptDoStep (scost : Option (NatInfoMap Nat)) (k : Nat) :
    Nat → CakeRaState → CakeRaState
  | 0, state => state
  | fuel + 1, state =>
      let (b, state) := cakeDoStep scost k state
      if b then cakeRptDoStep scost k fuel state else state

/-! ### Colour assignment and extraction (`reg_allocScript.sml:880-1450`) -/

/-- `remove_colours` (`reg_allocScript.sml:880-897`). -/
def cakeRemoveColours (state : CakeRaState) : List Nat → List Nat → List Nat
  | [], ks => ks
  | v :: vs, ks =>
      match cakeMapLookup state.nodeTag v with
      | some (.fixed c) => cakeRemoveColours state vs (ks.filter (· ≠ c))
      | _ => cakeRemoveColours state vs ks

/-- `first_match_col` (`reg_allocScript.sml:994-1004`). -/
def cakeFirstMatchCol (state : CakeRaState) (ks : List Nat) : List Nat → Option Nat
  | [] => none
  | v :: vs =>
      match cakeMapLookup state.nodeTag v with
      | some (.fixed m) => if ks.contains m then some m else cakeFirstMatchCol state ks vs
      | _ => cakeFirstMatchCol state ks vs

/-- `coalesce_root` (`reg_allocScript.sml:1363-1378`): read-only parent
    traversal without path compression. -/
def cakeCoalesceRoot : CakeRaState → Nat → Nat
  | state, x =>
      let xt := (cakeMapLookup state.coalesced x).getD x
      if cakeIsFixed state xt then xt
      else if _h : x <= xt then x
      else cakeCoalesceRoot state xt
termination_by _ x => x
decreasing_by all_goals omega

/-- `moves_to_sp` (`reg_allocScript.sml:1326-1345`): the move-partner
    table consulted by the biased colour preferences. -/
def cakeMovesToSp : List (Nat × (Nat × Nat)) →
    NatInfoMap (List (Nat × Nat)) → NatInfoMap (List (Nat × Nat))
  | [], table => table
  | (p, (x, y)) :: rest, table =>
      let table := cakeMapUpdate table x
        ((p, y) :: (cakeMapLookup table x).getD [])
      cakeMovesToSp rest
        (cakeMapUpdate table y ((p, x) :: (cakeMapLookup table y).getD []))

/-- `resort_moves` (`reg_allocScript.sml:1347-1350`): sort each partner
    list by descending priority, then drop the priorities. -/
def cakeResortMovesSp (table : NatInfoMap (List (Nat × Nat))) :
    NatInfoMap (List Nat) :=
  -- `cakeQSort`, not a stable sort: the original's `sort_moves` flips
  -- equal-priority entries (probes `sort_moves_probe.out`).
  table.map (fun entry =>
    (entry.1, (cakeQSort (fun a b => a.1 >= b.1) entry.2).map (·.2)))

/-- `update_move` (`reg_allocScript.sml:1407-1414`). -/
def cakeUpdateMove (spta : Nat → Nat) (move : Nat × (Nat × Nat)) :
    Nat × (Nat × Nat) :=
  let (p, (x, y)) := move
  let spx := spta x
  let spy := spta y
  if spx <= spy then (p, (spx, spy)) else (p, (spy, spx))

/-- `biased_pref` (`reg_allocScript.sml:1380-1395`). -/
def cakeBiasedPref (state : CakeRaState) (mtable : NatInfoMap (List Nat))
    (n : Nat) (ks : List Nat) : Option Nat :=
  if n < state.dim then
    let v := cakeCoalesceRoot state n
    let vs := (cakeMapLookup mtable n).getD []
    cakeFirstMatchCol state ks (v :: vs)
  else none

/-- `unbound_colour` (`reg_allocScript.sml:946-960`). -/
def cakeUnboundColour (col : Nat) : List Nat → Nat
  | [] => col
  | x :: xs =>
      if col < x then col
      else if col = x then cakeUnboundColour (col + 1) xs
      else cakeUnboundColour col xs

/-- `neg_first_match_col` (`reg_allocScript.sml:1420-1436`). -/
def cakeNegFirstMatchCol (state : CakeRaState) (k : Nat) (bads : List Nat) :
    List Nat → Option Nat
  | [] => none
  | m :: ms =>
      match cakeMapLookup state.nodeTag m with
      | some (.fixed c) =>
          if bads.contains c || c < k then cakeNegFirstMatchCol state k bads ms
          else some c
      | some _ => cakeNegFirstMatchCol state k bads ms
      | none => none

/-- `neg_biased_pref` (`reg_allocScript.sml:1438-1450`). -/
def cakeNegBiasedPref (state : CakeRaState) (k : Nat)
    (mtable : NatInfoMap (List Nat)) (n : Nat) (bads : List Nat) : Option Nat :=
  if n < state.dim then
    match cakeMapLookup mtable n with
    | none => none
    | some vs => cakeNegFirstMatchCol state k bads vs
  else none

/-- `tag_col` (`reg_allocScript.sml:941-944`). -/
def cakeTagCol (state : CakeRaState) (v : Nat) : Nat :=
  match cakeMapLookup state.nodeTag v with
  | some (.fixed m) => m
  | _ => 0

/-- `assign_Atemp_tag` (`reg_allocScript.sml:903-927`). -/
def cakeAssignAtempTag (k : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (n : Nat)
    (state : CakeRaState) : CakeRaState :=
  match cakeMapLookup state.nodeTag n with
  | some .aTemp =>
      let ks' := cakeRemoveColours state (cakeAdjSub state.adjLists n) (List.range k)
      match ks' with
      | [] => { state with nodeTag := cakeMapUpdate state.nodeTag n .sTemp }
      | c :: _ =>
          match prefs state n ks' with
          | none => { state with nodeTag := cakeMapUpdate state.nodeTag n (.fixed c) }
          | some y => { state with nodeTag := cakeMapUpdate state.nodeTag n (.fixed y) }
  | _ => state

/-- `assign_Atemps` (`reg_allocScript.sml:923-938`). -/
def cakeAssignAtemps (k : Nat) (ls : List Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat)
    (state : CakeRaState) : CakeRaState :=
  /- Cake's state-stack is consumed in the order in which entries were
     pushed by the worklist traversal; the functional list stores that order
     newest-first, so restore the traversal order before assigning colours. -/
  let lsF := ls.reverse.filter (· < state.dim)
  let state := lsF.foldl (fun s n => cakeAssignAtempTag k prefs n s) state
  (List.range state.dim).foldl (fun s n => cakeAssignAtempTag k prefs n s) state

/-- `assign_Stemp_tag` (`reg_allocScript.sml:962-982`). -/
def cakeAssignStempTag (k : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (n : Nat)
    (state : CakeRaState) : CakeRaState :=
  match cakeMapLookup state.nodeTag n with
  | some .sTemp =>
      let bads := (cakeAdjSub state.adjLists n).map (fun v => cakeTagCol state v)
        |>.mergeSort (fun a b => a < b)
      match prefs state n bads with
      | none =>
          { state with
            nodeTag := cakeMapUpdate state.nodeTag n (.fixed (cakeUnboundColour k bads)) }
      | some y =>
          { state with nodeTag := cakeMapUpdate state.nodeTag n (.fixed y) }
  | _ => state

/-- `assign_Stemps` (`reg_allocScript.sml:984-990`). -/
def cakeAssignStemps (k : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat)
    (state : CakeRaState) : CakeRaState :=
  (List.range state.dim).foldl (fun s n => cakeAssignStempTag k prefs n s) state

/-- `extract_color` (`reg_allocScript.sml:1306-1320`): the var → colour
    table over the (ascending) allocator bijection. -/
def cakeExtractColor (state : CakeRaState) (toAllocator : NatInfoMap Nat) :
    NatInfoMap Nat :=
  (toAllocator.mergeSort (fun a b => a.1 < b.1)).foldl (fun acc entry =>
      cakeMapUpdate acc entry.1 (cakeTagCol state entry.2)) []

/-- `full_consistency_ok` (`reg_allocScript.sml:1385+`). -/
def cakeTagIsAtemp (state : CakeRaState) (x : Nat) : Bool :=
  match cakeMapLookup state.nodeTag x with
  | some .aTemp => true
  | _ => false

def cakeFullConsistencyOk (state : CakeRaState) (k : Nat) (x y : Nat) : Bool :=
  x != y && x < state.dim && y < state.dim &&
    !(cakeAdjSub state.adjLists y).contains x &&
    (cakeIsFixedK state k x || cakeTagIsAtemp state x) &&
    (cakeIsFixedK state k y || cakeTagIsAtemp state y) &&
    !(cakeIsFixedK state k x && cakeIsFixedK state k y)

/-- The allocator flavour, mirroring `algorithm` in the original. -/
inductive CakeAlgorithm : Type
  | simple : CakeAlgorithm
  | irc : CakeAlgorithm

/-- `do_reg_alloc` (`reg_allocScript.sml:1452-1470`): the complete IRC
    colouring pipeline over a clash tree, producing the var → colour
    table. -/
def cakeDoRegAlloc (alg : CakeAlgorithm) (scost : Option (NatInfoMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) : Option (NatInfoMap Nat) :=
  let bij := cakeMkBij tree
  let state := cakeInitRaState tree forced fs
  let spta := fun v => (cakeMapLookup bij.toAllocator v).getD 0
  let moves0 := moves.map (cakeUpdateMove spta)
  let movesF := filterReversed (fun m => cakeFullConsistencyOk state k m.2.1 m.2.2) moves0
  let selMoves := match alg with
    | .simple => []
    | .irc => movesF
  let (l, s0) := cakeInitAlloc1Heu selMoves k state
  let s1 := cakeRptDoStep scost k l s0
  let ls := s1.stack
  let mvs := cakeResortMovesSp (cakeMovesToSp moves0 [])
  let state := cakeAssignAtemps k ls (fun s n ks => cakeBiasedPref s mvs n ks) s1
  let state := cakeAssignStemps k (fun s n bads => cakeNegBiasedPref s k mvs n bads) state
  some (cakeExtractColor state bij.toAllocator)

/-! Convert Cake's `total_colour` result back into the location contract used
    by Word-to-Stack.  Cake colours are even Word names; their half is the
    abstract Cake stack-register number and must remain unchanged until the
    Lab-to-RISC-V boundary applies `riscv_names`.  Colours outside the
    allocatable window are frame variables numbered from the top of Cake's
    `f` frame. -/

def cakeColourLocation (k f colour : Nat) : WordLocation :=
  let stackRegister := colour / 2
  if stackRegister < k then
    .register stackRegister
  else
    .stack (f - 1 - (stackRegister - k))

def cakeColourFrameSlots (k : Nat) (parameters : List Nat)
    (program : WordProg α) (colouring : NatInfoMap Nat) : Nat × Nat :=
  let colour := CakeAlloc.totalColour colouring
  let coloured := wordApplyColour colour program
  let maxVar := (wordProgVariables coloured).foldl max 0
  let stackArgs := parameters.length - k
  let f' := max ((maxVar / 2 + 1) - k) stackArgs
  (f', if f' = 0 then 0 else f' + 1)

def cakeColourWordSpillState (k : Nat) (parameters : List Nat)
    (program : WordProg α) (colouring : NatInfoMap Nat) : WordSpillState :=
  let colour := CakeAlloc.totalColour colouring
  let (_, f) := cakeColourFrameSlots k parameters program colouring
  let names := (parameters ++ wordProgVariables program).eraseDups
  let locations := names.map (fun name =>
    (name, cakeColourLocation k f (colour name)))
  { locations, nextSpill := if f = 0 then 0 else f - 1 }

/-! Production-facing Cake allocator adapter.  This keeps Cake's full SSA
    entry moves and IRC coalescing in the returned Word program, while
    exposing the existing `WordSpillState` shape to the shared pipeline. -/

def cakeAllocateWordFunction [OfNat α 0] (parameters : List Nat) (program : WordProg α)
    (currentFunction : Nat) (k : Nat) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans parameters.length program
  let tree := wordClashTree ssaProgram []
  let fs := cakeGetStackOnly ssaProgram
  let forced := cakeGetForced ssaProgram
  let (wordMoves, spillCosts) := wordGetHeuristics 3 currentFunction ssaProgram
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (fun costs =>
    costs.filterMap (fun entry =>
      (lookupNatInfo entry.1 bij.toAllocator).map
        (fun node => (node, entry.2))))
  match cakeDoRegAlloc .irc scost k moves tree forced fs with
  | none => none
  | some colouring =>
      some (state, renamedParameters, ssaProgram,
        cakeColourWordSpillState k parameters ssaProgram colouring)

/-! `get_prefs` from the original allocator driver: the move preferences fed
    to IRC (`word_allocScript.sml:1203-1215` via `get_heuristics_def`). -/
def cakeGetPrefs {α : Type u} [OfNat α 0] [OfNat α 1] :
    WordProg α → List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat))
  | .move priority moves, acc =>
      moves.foldl (fun acc' move => (priority, (move.1, move.2)) :: acc') acc
  | .mustTerminate body, acc => cakeGetPrefs body acc
  | .seq first second, acc => cakeGetPrefs first (cakeGetPrefs second acc)
  | .ite _ _ _ thenBranch elseBranch, acc =>
      cakeGetPrefs thenBranch (cakeGetPrefs elseBranch acc)
  | .call (some (_, _, returnHandler, _, _)) _ _ handler, acc =>
      match handler with
      | none => cakeGetPrefs returnHandler acc
      | some (_, handlerBody, _, _) =>
          cakeGetPrefs handlerBody (cakeGetPrefs returnHandler acc)
  | .loop _ body _, acc => cakeGetPrefs body acc
  | _, acc => acc
  termination_by program _ => sizeOf program
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-! Frame occupancy from a full Cake IRC run, mirroring the original
    `word_to_stack$compile_prog` stack-variable count
    (`word_to_stackScript.sml:586-600`): the colouring rewrites spilled
    variables to stack numbers `2*k + 2*slot`, so `max_var DIV 2 + 1 - k`
    counts them, floored by the stack-argument area.  Returns the exact
    `stack_var_count` (the bitmap writer's `f'`); zero means the original
    would skip the bitmap entirely.  The bitmap live set itself comes from
    the exception cut set (`wLive` consumes `SND live`), which the pancake
    pipeline always leaves empty, so the emitted words stay pure powers of
    two independently of the production register-location map. -/
def cakeWordStackVarCount [OfNat α 0] [OfNat α 1]
    (currentFunction : Nat) (parameters : List Nat) (k : Nat)
    (program : WordProg α) : Nat :=
  let ssaProgram := (wordFullSsaCcTrans parameters.length program).2.2
  let tree := wordClashTree ssaProgram []
  let fs := cakeGetStackOnly ssaProgram
  let forced := cakeGetForced ssaProgram
  let (wordMoves, spillCosts) := wordGetHeuristics 3 currentFunction ssaProgram
  let moves := wordMoves.map (fun m => (m.priority, (m.left, m.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (fun costs =>
    costs.filterMap (fun entry =>
      (lookupNatInfo entry.1 bij.toAllocator).map
        (fun node => (node, entry.2))))
  match cakeDoRegAlloc .irc scost k moves tree forced fs with
  | none => 0
  | some colouring =>
      let colour := CakeAlloc.totalColour colouring
      let coloured := wordApplyColour colour ssaProgram
      let maxVar := (wordProgVariables coloured).foldl max 0
      let stackArgs := parameters.length - k
      max ((maxVar / 2 + 1) - k) stackArgs

end Flapjack.RiscV.CakeRegAlloc
