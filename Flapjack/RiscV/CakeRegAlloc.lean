import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.Allocator
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
      | some names => cakeListRemap names mapped
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
  availMovesWl : List (Nat × Nat)
  unavailMovesWl : List (Nat × Nat)
  stack : List Nat
  deriving Repr

/-- The empty allocator state for `n` nodes. -/
def CakeRaState.empty (n : Nat) : CakeRaState :=
  { adjLists := [], nodeTag := [], degrees := [], coalesced := [],
    moveRelated := [], dim := n, simpWl := [], spillWl := [], freezeWl := [],
    availMovesWl := [], unavailMovesWl := [], stack := [] }

/-- Newest-wins functional update of a `NatInfoMap`. -/
def cakeMapUpdate {α : Type u} (m : NatInfoMap α) (i : Nat) (v : α) : NatInfoMap α :=
  (i, v) :: m

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
      | some t => (cakeCliqueInsertEdge (t.map ta) adj2, t.map ta)
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
      let v := (cakeMapLookup fromAllocator i).getD 0
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
end Flapjack.RiscV.CakeRegAlloc
