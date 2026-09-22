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
  getForcedAddCarry getForcedLongMul isAllocVar isPhyVar isStackVar)

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

/-! Fast internal form for the stack-only analysis.  The lists remain the
    Cake-visible ordered representation; the carried sets only accelerate
    membership and set algebra. -/
structure CakeStackOnlyState where
  ts : List Nat
  fs : List Nat
  tsSet : Std.TreeSet Nat
  fsSet : Std.TreeSet Nat

def cakeStackOnlyStateOfPair (tfs : List Nat × List Nat) : CakeStackOnlyState :=
  { ts := tfs.1, fs := tfs.2,
    tsSet := Flapjack.natSetOfList tfs.1,
    fsSet := Flapjack.natSetOfList tfs.2 }

def cakeStackOnlyInsert (x : Nat) (xs : List Nat)
    (seen : Std.TreeSet Nat) : List Nat × Std.TreeSet Nat :=
  if seen.contains x then (xs, seen) else (x :: xs, seen.insert x)

def cakeStackOnlyDelete (x : Nat) (xs : List Nat)
    (seen : Std.TreeSet Nat) : List Nat × Std.TreeSet Nat :=
  (xs.erase x, seen.erase x)

def cakeStackOnlyMergeMove (x y : Nat) (state : CakeStackOnlyState) :
    CakeStackOnlyState :=
  if state.tsSet.contains x then
    let (ts, tsSet) := if isAllocVar y then
      cakeStackOnlyInsert y state.ts state.tsSet else (state.ts, state.tsSet)
    let (fs, fsSet) := if !isPhyVar y then
      cakeStackOnlyInsert x state.fs state.fsSet else (state.fs, state.fsSet)
    { state with ts, fs, tsSet, fsSet }
  else if isStackVar x then
    let (ts, tsSet) := if isAllocVar y then
      cakeStackOnlyInsert y state.ts state.tsSet else (state.ts, state.tsSet)
    { state with ts, tsSet }
  else
    let (ts, tsSet) := cakeStackOnlyDelete y state.ts state.tsSet
    { state with ts, tsSet }

def cakeStackOnlyUnion (left : List Nat) (leftSet : Std.TreeSet Nat)
    (right : List Nat) : List Nat × Std.TreeSet Nat :=
  (left ++ right.filter (fun x => !leftSet.contains x),
   right.foldl (fun seen x => seen.insert x) leftSet)

def cakeStackOnlyDiff (left : List Nat) (leftSet rightSet : Std.TreeSet Nat)
    (right : List Nat) : List Nat × Std.TreeSet Nat :=
  (left.filter (fun x => !rightSet.contains x),
   right.foldl (fun seen x => seen.erase x) leftSet)

def cakeStackOnlyInter (left : List Nat) (rightSet : Std.TreeSet Nat) :
    List Nat × Std.TreeSet Nat :=
  let kept := left.filter (fun x => rightSet.contains x)
  (kept, Flapjack.natSetOfList kept)

def cakeStackOnlyMergeSetsReference (base left right : CakeStackOnlyState) :
    CakeStackOnlyState :=
  let (_inner, innerSet) := cakeStackOnlyInter left.ts base.tsSet
  let (common, commonSet) := cakeStackOnlyInter right.ts innerSet
  let (leftOnly, leftOnlySet) :=
    cakeStackOnlyDiff left.ts left.tsSet base.tsSet base.ts
  let (rightOnly, _rightOnlySet) :=
    cakeStackOnlyDiff right.ts right.tsSet base.tsSet base.ts
  let (different, _differentSet) :=
    cakeStackOnlyUnion leftOnly leftOnlySet rightOnly
  let (ts, tsSet) := cakeStackOnlyUnion common commonSet different
  let (fs, fsSet) := cakeStackOnlyUnion left.fs left.fsSet right.fs
  { ts, fs, tsSet, fsSet }

/-! The two `Diff` results below are consumed only through their list
    projections. Keep the Cake list order, but avoid constructing the
    discarded intermediate TreeSets; the final union still rebuilds exactly
    the same sets as the reference. -/
def cakeStackOnlyMergeSets (base left right : CakeStackOnlyState) :
    CakeStackOnlyState :=
  let (_inner, innerSet) := cakeStackOnlyInter left.ts base.tsSet
  let (common, commonSet) := cakeStackOnlyInter right.ts innerSet
  let leftOnly := left.ts.filter (fun x => !base.tsSet.contains x)
  let leftOnlySet := Flapjack.natSetOfList leftOnly
  let rightOnly := right.ts.filter (fun x => !base.tsSet.contains x)
  let different := leftOnly ++ rightOnly.filter (fun x => !leftOnlySet.contains x)
  let ts := common ++ different.filter (fun x => !commonSet.contains x)
  let tsSet := different.foldl (fun seen x => seen.insert x) commonSet
  let fs := left.fs ++ right.fs.filter (fun x => !left.fsSet.contains x)
  let fsSet := right.fs.foldl (fun seen x => seen.insert x) left.fsSet
  { ts, fs, tsSet, fsSet }

def cakeStackOnlyDeleteMany (names : List Nat) (state : CakeStackOnlyState) :
    CakeStackOnlyState :=
  names.foldr (fun name state =>
    let (ts, tsSet) := cakeStackOnlyDelete name state.ts state.tsSet
    { state with ts, tsSet }) state

def cakeGetStackOnlyAuxFast {α : Type u} :
    CakeStackOnlyState → WordProg α → CakeStackOnlyState
  | state, .skip => state
  | state, .move _ moves =>
      moves.foldr (fun move state => cakeStackOnlyMergeMove move.1 move.2 state) state
  | state, .seq first second =>
      cakeGetStackOnlyAuxFast (cakeGetStackOnlyAuxFast state second) first
  | state, .ite _ condition right thenBranch elseBranch =>
      let left := cakeGetStackOnlyAuxFast state thenBranch
      let rightState := cakeGetStackOnlyAuxFast state elseBranch
      let merged := cakeStackOnlyMergeSets state left rightState
      cakeStackOnlyDeleteMany
        (condition :: match right with | .reg name => [name] | .imm _ => []) merged
  | state, .mustTerminate body => cakeGetStackOnlyAuxFast state body
  | state, .call (some (_, _, returnHandler, _, _)) _ _ handler =>
      let returnState := cakeGetStackOnlyAuxFast state returnHandler
      match handler with
      | none => returnState
      | some (_, handlerBody, _, _) =>
          cakeStackOnlyMergeSets state returnState
            (cakeGetStackOnlyAuxFast state handlerBody)
  | state, .call none _ _ _ => state
  | state, .loop _ body _ => cakeGetStackOnlyAuxFast state body
  | state, .tick => state
  | state, .break _ => state
  | state, .continue _ => state
  | state, program =>
      match wordClashTree program [] with
      | .delta writes reads => cakeStackOnlyDeleteMany (writes ++ reads) state
      | _ => state
  termination_by _state program => sizeOf program
  decreasing_by
    all_goals first
      | sizeOf_list_dec | decreasing_tactic | decreasing_trivial
        <;> simp_arith

/-- `get_stack_only` (`word_allocScript.sml:1787-1789`): the forced-stack
    variable list for a whole program. -/
def cakeGetStackOnly {α : Type u} (program : WordProg α) : List Nat :=
  (cakeGetStackOnlyAuxFast (cakeStackOnlyStateOfPair ([], [])) program).fs

/-! RISC-V `get_forced` traversal.  The source adds hardware interference
    edges for the carry and long-multiply instructions, then walks sequence,
    branch, call-handler, and loop bodies in reverse continuation order. -/
def cakeForcedArith {α : Type u} : WordArith α → List (Nat × Nat)
  | .addCarry destination _ _ sourceRight carryIn =>
      getForcedAddCarry destination sourceRight carryIn
  | .cakeAddCarry destination _ sourceRight carry =>
      getForcedAddCarry destination sourceRight carry
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

/- The reference keeps the two observable association-list maps in
   first-appearance order.  The membership test used while constructing them
   need not rescan that history, so the production constructor carries a
   private ordered index and drops it at the public boundary. -/
structure CakeNodeBijectionBuild where
  toAllocator : NatInfoMap Nat
  fromAllocator : NatInfoMap Nat
  index : Std.TreeMap Nat Nat
  nextNode : Nat

def cakeListRemapBuild : List Nat → CakeNodeBijectionBuild → CakeNodeBijectionBuild
  | [], bijection => bijection
  | name :: names, bijection =>
      match bijection.index[name]? with
      | some _ => cakeListRemapBuild names bijection
      | none =>
          cakeListRemapBuild names
            { toAllocator := (name, bijection.nextNode) :: bijection.toAllocator
              fromAllocator := (bijection.nextNode, name) :: bijection.fromAllocator
              index := bijection.index.insert name bijection.nextNode
              nextNode := bijection.nextNode + 1 }

def cakeMkBijBuildAux : WordClashTree → CakeNodeBijectionBuild → CakeNodeBijectionBuild
  | .delta writes reads, bijection =>
      cakeListRemapBuild writes (cakeListRemapBuild reads bijection)
  | .set names, bijection =>
      cakeListRemapBuild (NumSet.fromAList names) bijection
  | .branch live thenBranch elseBranch, bijection =>
      let mapped := cakeMkBijBuildAux elseBranch
        (cakeMkBijBuildAux thenBranch bijection)
      match live with
      | none => mapped
      | some names => cakeListRemapBuild (NumSet.fromAList names) mapped
  | .seq first second, bijection =>
      cakeMkBijBuildAux first (cakeMkBijBuildAux second bijection)

def cakeMkBijBuild (tree : WordClashTree) : CakeNodeBijectionBuild :=
  cakeMkBijBuildAux tree
    { toAllocator := [], fromAllocator := [], index := {}, nextNode := 0 }

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

/- A lookup-only index for the source-variable side of `mk_bij`.  Cake's
   association list remains the canonical representation; this index is used
   only by repeated `sp_default` lookups while constructing the graph and
   node tags. -/
def cakeSpDefaultIndex (entries : NatInfoMap Nat) : Std.HashMap Nat Nat :=
  entries.foldl (fun index entry =>
    match index[entry.1]? with
    | some _ => index
    | none => index.insert entry.1 entry.2) {}

def cakeSpDefaultIndexed (index : Std.HashMap Nat Nat) (n : Nat) : Nat :=
  match index[n]? with
  | some colour => colour
  | none => if CakeAlloc.isPhyVar n then n / 2 else 0

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
      /- A Cake `Set` is a Patricia-tree `num_set`, not an ordered list.
         `mk_bij_aux` enumerates it with `MAP FST (toAList t)`, whose order
         is the mixed Patricia traversal reconstructed by `NumSet.fromAList`.
         Sorting here changes allocator node numbering and therefore can
         change otherwise valid register-colour tie breaks. -/
      cakeListRemap (NumSet.fromAList names) bijection
  | .branch live thenBranch elseBranch, bijection =>
      let mapped := cakeMkBijAux elseBranch (cakeMkBijAux thenBranch bijection)
      match live with
      | none => mapped
      | some names =>
          cakeListRemap (NumSet.fromAList names) mapped
  | .seq first second, bijection => cakeMkBijAux first (cakeMkBijAux second bijection)

/-- `mk_bij` (`reg_allocScript.sml:1119-1127`): the node bijection for a
    whole clash tree, starting from the empty bijection at node zero. -/
def cakeMkBij (tree : WordClashTree) : CakeNodeBijection :=
  let built := cakeMkBijBuild tree
  { toAllocator := built.toAllocator,
    fromAllocator := built.fromAllocator,
    nextNode := built.nextNode }

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

/-! ### Node-indexed allocator fields

`reg_allocScript.sml:61-78` declares `adj_ls`, `node_tag`, `degrees`,
`coalesced` and `move_related` as arrays indexed by node id, reached through
`sub`/`update` in the allocator's state monad.  Holding them as association
lists made every degree read and every edge insertion a linear scan, so a
single `do_spill` over a 6361-node worklist cost 6361 scans of a 6361-entry
list, and the real guest's largest function did not finish in 90 minutes.

`CakeNodeMap` is the array representation.  `slots` holds one entry per node,
`none` where the list version had no binding yet; `outside` keeps the keys at
or above the dimension, which the list version reached by appending.  `get`
and `set` therefore agree with `cakeMapLookup` and `cakeMapUpdate` on every
key, so nothing observable changes. -/
structure CakeNodeMap (α : Type u) where
  slots : Array (Option α) := #[]
  outside : NatInfoMap α := []
  deriving Repr

namespace CakeNodeMap

/-- `sub` (`reg_allocScript.sml` array accessors). -/
def get {α : Type u} (m : CakeNodeMap α) (i : Nat) : Option α :=
  if h : i < m.slots.size then m.slots[i] else cakeMapLookup m.outside i

/-- `update`. -/
def set {α : Type u} (m : CakeNodeMap α) (i : Nat) (v : α) : CakeNodeMap α :=
  if i < m.slots.size then { m with slots := m.slots.set! i (some v) }
  else { m with outside := cakeMapUpdate m.outside i v }

/-- An `n`-node field with no bindings yet, matching the empty list. -/
def ofSize {α : Type u} (n : Nat) : CakeNodeMap α :=
  { slots := Array.replicate n none }

/-- The association list read as a node-indexed field.  `cakeMapLookup`
    returns the *first* binding for a key, so the earlier entries must win;
    folding from the right lets them overwrite the later ones. -/
def ofNatInfoMap {α : Type u} (n : Nat) (m : NatInfoMap α) : CakeNodeMap α :=
  m.foldr (fun entry acc => acc.set entry.1 entry.2) (ofSize n)

/-- Rebuild every entry with `f`, leaving the indexing alone. -/
def mapValues {α : Type u} {β : Type v} (f : α → β) (m : CakeNodeMap α) :
    CakeNodeMap β :=
  { slots := m.slots.map (fun entry => entry.map f)
    outside := m.outside.map (fun entry => (entry.1, f entry.2)) }

/-- The field read back as an association list, ascending by node, for
    diagnostics.  Every key keeps the value `get` returns for it. -/
def toNatInfoMap {α : Type u} (m : CakeNodeMap α) : NatInfoMap α :=
  (List.range m.slots.size).filterMap
    (fun i => (m.get i).map (fun v => (i, v))) ++ m.outside

end CakeNodeMap

def cakeSpillCostMap (nextNode : Nat) (costs : NatInfoMap Nat) : CakeNodeMap Nat :=
  CakeNodeMap.ofNatInfoMap nextNode costs

/- Cake passes the source-keyed spill-cost tree directly to `reg_alloc`.
   `CakeNodeMap` therefore must retain a cost whose source key lies beyond
   the allocator-node array in its `outside` map; silently densifying that
   key would change `st_ex_list_MIN_cost` selection. -/
theorem cakeSpillCostMap_outside_lookup
    (nextNode key cost : Nat) (hkey : nextNode ≤ key) :
    (cakeSpillCostMap nextNode [(key, cost)]).get key = some cost := by
  have hlt : ¬ key < nextNode := Nat.not_lt_of_ge hkey
  simp [cakeSpillCostMap, CakeNodeMap.ofNatInfoMap, CakeNodeMap.set,
    CakeNodeMap.get, CakeNodeMap.ofSize, cakeMapUpdate, cakeMapLookup,
    Flapjack.lookupNatInfo,
    hlt]

/-- The IRC allocator state (`ra_state`), represented functionally. -/
structure CakeRaState where
  adjLists : CakeNodeMap (List Nat)
  /- Present for production states built by `cakeInitRaStateFromBij`; hand-
     constructed proof/test states leave it absent and use `adjLists`. -/
  adjSets : Option (CakeNodeMap (Std.TreeSet Nat))
  nodeTag : CakeNodeMap CakeNodeTag
  degrees : CakeNodeMap Nat
  coalesced : CakeNodeMap Nat
  moveRelated : CakeNodeMap Bool
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
  { adjLists := CakeNodeMap.ofSize n, adjSets := none,
    nodeTag := CakeNodeMap.ofSize n,
    degrees := CakeNodeMap.ofSize n, coalesced := CakeNodeMap.ofSize n,
    moveRelated := CakeNodeMap.ofSize n, dim := n,
    simpWl := [], spillWl := [], freezeWl := [],
    availMovesWl := [], unavailMovesWl := [], stack := [] }

/-- `sorted_insert` (`reg_allocScript.sml:184-189`): insert into a
    descending adjacency list, skipping duplicates. -/
def cakeSortedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x = y then y :: ys
      else if x > y then x :: y :: ys
      else y :: cakeSortedInsert x ys

/-- `sorted_mem` (`reg_allocScript.sml:193-198`): membership in a descending
    adjacency list, stopping as soon as the list passes the sought key.  The
    adjacency lists are kept descending by `cakeSortedInsert`, so on them this
    agrees with `List.contains`; it is what the original computes, and the
    early exit is why the original's coalescing scans stay cheap. -/
def cakeSortedMem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys =>
      if x = y then true
      else if x > y then false
      else cakeSortedMem x ys

/-- Adjacency list of node `i` (`adj_ls_sub`). -/
def cakeAdjSub (adj : CakeNodeMap (List Nat)) (i : Nat) : List Nat :=
  (adj.get i).getD []

def cakeAdjMem (state : CakeRaState) (x y : Nat) : Bool :=
  match state.adjSets with
  | some adj => ((adj.get y).getD ∅).contains x
  | none => cakeSortedMem x (cakeAdjSub state.adjLists y)

/-- `adj_ls_sub` on the association-list form still used while the graph is
    being built, before it is read into the node-indexed field. -/
def cakeAdjSubList (adj : NatInfoMap (List Nat)) (i : Nat) : List Nat :=
  (cakeMapLookup adj i).getD []

/-- `insert_edge` (`reg_allocScript.sml:201-212`): undirected edge into the
    adjacency representation.  Both neighbour lists are read before either
    slot is written, so the array is not aliased across the update and the
    write stays in place. -/
def cakeInsertEdge (x y : Nat) (adj : CakeNodeMap (List Nat)) :
    CakeNodeMap (List Nat) :=
  let adjX := cakeAdjSub adj x
  let adjY := cakeAdjSub adj y
  (adj.set x (cakeSortedInsert y adjX)).set y (cakeSortedInsert x adjY)

/-- `list_insert_edge` (`reg_allocScript.sml:214-221`). -/
def cakeListInsertEdge (x : Nat) : List Nat → CakeNodeMap (List Nat) →
    CakeNodeMap (List Nat)
  | [], adj => adj
  | y :: ys, adj => cakeListInsertEdge x ys (cakeInsertEdge x y adj)

/-- `clique_insert_edge` (`reg_allocScript.sml:223-232`). -/
def cakeCliqueInsertEdge : List Nat → CakeNodeMap (List Nat) →
    CakeNodeMap (List Nat)
  | [], adj => adj
  | x :: xs, adj => cakeCliqueInsertEdge xs (cakeListInsertEdge x xs adj)

/-- `extend_clique` (`reg_allocScript.sml:235-249`): extend an existing
    clique with new members, returning the extended live list. -/
def cakeExtendClique : List Nat → List Nat → CakeNodeMap (List Nat) →
    CakeNodeMap (List Nat) × List Nat
  | [], cli, adj => (adj, cli)
  | x :: xs, cli, adj =>
      if cli.contains x then cakeExtendClique xs cli adj
      else cakeExtendClique xs (x :: cli) (cakeListInsertEdge x cli adj)
termination_by new _ _ => sizeOf new
decreasing_by all_goals decreasing_trivial

/- The reference inserts each pair in a growing clique. For the TreeSet
   accumulator, union the new node's partners once, then add the reverse
   edge to each existing member. Overlap handling preserves the reference
   live-list and graph behavior for duplicate names. -/
def cakeExtendCliqueSetFastAux : List Nat → List Nat → Std.TreeSet Nat →
    CakeNodeMap (Std.TreeSet Nat) → CakeNodeMap (Std.TreeSet Nat) × List Nat
  | [], cli, _members, adj => (adj, cli)
  | x :: xs, cli, members, adj =>
      if members.contains x then
        cakeExtendCliqueSetFastAux xs cli members adj
      else
        let existingX := (adj.get x).getD ∅
        let adjX := adj.set x (existingX.union members)
        let adjAll := cli.foldl (fun current y =>
          let existingY := (current.get y).getD ∅
          current.set y (existingY.insert x)) adjX
        cakeExtendCliqueSetFastAux xs (x :: cli) (members.insert x) adjAll
termination_by new _ _ _ => sizeOf new
decreasing_by all_goals decreasing_trivial

/- Batch the set unions performed by `cakeExtendCliqueSetFastAux`.  The
   reference adds each admitted node to every existing member in turn; since
   adjacency is a TreeSet, unioning the complete admitted set gives the same
   graph, while `addedRev ++ cli` preserves the reference's newest-first live
   list.  Duplicate names are collected with the same first-admission rule. -/
def cakeExtendCliqueSetBatch (new : List Nat) (cli : List Nat)
    (adj : CakeNodeMap (Std.TreeSet Nat)) :
    CakeNodeMap (Std.TreeSet Nat) × List Nat :=
  let initial := Std.TreeSet.ofList cli
  let (members, addedRev) := new.foldl (fun (state : Std.TreeSet Nat × List Nat) x =>
    let (seen, added) := state
    if seen.contains x then (seen, added)
    else (seen.insert x, x :: added)) (initial, [])
  let addedSet := Std.TreeSet.ofList addedRev
  let adjNew := addedRev.foldl (fun current x =>
    let existing := (current.get x).getD ∅
    current.set x (existing.union (members.erase x))) adj
  let adjAll := cli.foldl (fun current y =>
    let existing := (current.get y).getD ∅
    current.set y (existing.union addedSet)) adjNew
  (adjAll, addedRev ++ cli)

def cakeExtendCliqueSetFast : List Nat → List Nat →
    CakeNodeMap (Std.TreeSet Nat) → CakeNodeMap (Std.TreeSet Nat) × List Nat
  | new, cli, adj =>
      cakeExtendCliqueSetBatch new cli adj

def cakeExtendCliqueSet : List Nat → List Nat →
    CakeNodeMap (Std.TreeSet Nat) → CakeNodeMap (Std.TreeSet Nat) × List Nat :=
  cakeExtendCliqueSetFast

/-- `mk_graph` (`reg_allocScript.sml:1179-1218`): build the adjacency
    representation from a clash tree, threading the live list.  `ta` maps
    original variable names to node ids (`sp_default` over the bijection).
    The `Set` case walks the original sptree keys in ascending order, so the
    fixed clash-tree set is sorted at this boundary like in `cakeMkBijAux`. -/
def cakeMkGraph (ta : Nat → Nat) : WordClashTree → List Nat →
    CakeNodeMap (List Nat) → CakeNodeMap (List Nat) × List Nat
  | .delta writes reads, liveout, adj =>
      let wta := writes.map ta
      let rta := reads.map ta
      let (adj1, live) := cakeExtendClique wta liveout adj
      cakeExtendClique rta (live.filter (fun x => !wta.contains x)) adj1
  | .set names, _liveout, adj =>
      let live := (NumSet.fromAList names).map ta
      (cakeCliqueInsertEdge live adj, live)
  | .branch topt t1 t2, liveout, adj =>
      let (adj1, t1Live) := cakeMkGraph ta t1 liveout adj
      let (adj2, t2Live) := cakeMkGraph ta t2 liveout adj1
      match topt with
      | none => cakeExtendClique t1Live t2Live adj2
      | some t =>
          let live := (NumSet.fromAList t).map ta
          (cakeCliqueInsertEdge live adj2, live)
  | .seq t1 t2, liveout, adj =>
      let (adj1, live) := cakeMkGraph ta t2 liveout adj
      cakeMkGraph ta t1 live adj1
termination_by tree _ _ => sizeOf tree
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `extend_graph` (`reg_allocScript.sml:1224-1230`): add the forced edges. -/
def cakeExtendGraph (ta : Nat → Nat) : List (Nat × Nat) →
    CakeNodeMap (List Nat) → CakeNodeMap (List Nat)
  | [], adj => adj
  | (x, y) :: rest, adj =>
      cakeExtendGraph ta rest (cakeInsertEdge (ta x) (ta y) adj)

/-! Cake's observable adjacency lists are sorted
    descending sets.  Accumulating those sets in TreeSets avoids rescanning a
    long sorted list for every edge, then materializes the same list shape once
    at the allocator boundary.  The live-list traversal above is deliberately
    shared in shape and order with the reference builder. -/
def cakeAdjSetMapOfSize (n : Nat) : CakeNodeMap (Std.TreeSet Nat) :=
  { slots := Array.replicate n (some (∅ : Std.TreeSet Nat)) }

def cakeAdjSetList (s : Std.TreeSet Nat) : List Nat := s.toList.reverse

def cakeInsertEdgeSet (x y : Nat) (adj : CakeNodeMap (Std.TreeSet Nat)) :
    CakeNodeMap (Std.TreeSet Nat) :=
  let adjX := (adj.get x).getD ∅
  let adjY := (adj.get y).getD ∅
  (adj.set x (adjX.insert y)).set y (adjY.insert x)

def cakeListInsertEdgeSet (x : Nat) : List Nat →
    CakeNodeMap (Std.TreeSet Nat) → CakeNodeMap (Std.TreeSet Nat)
  | [], adj => adj
  | y :: ys, adj => cakeListInsertEdgeSet x ys (cakeInsertEdgeSet x y adj)

def cakeCliqueInsertEdgeSet : List Nat → CakeNodeMap (Std.TreeSet Nat) →
    CakeNodeMap (Std.TreeSet Nat)
  | [], adj => adj
  | x :: xs, adj => cakeCliqueInsertEdgeSet xs (cakeListInsertEdgeSet x xs adj)

/- For the duplicate-free sets produced by `NumSet.fromAList`, every node in
   a clique receives the same partner set minus itself.  Unioning that set
   once per node preserves the TreeSet graph while avoiding one insertion per
   unordered pair.  Duplicate inputs retain the reference path exactly. -/
def cakeCliqueInsertEdgeSetFast (live : List Nat)
    (adj : CakeNodeMap (Std.TreeSet Nat)) : CakeNodeMap (Std.TreeSet Nat) :=
  if h : live.Nodup then
    let all := Std.TreeSet.ofList live
    live.foldl (fun current x =>
      let partners := all.erase x
      let existing := (current.get x).getD ∅
      current.set x (existing.union partners)) adj
  else
    cakeCliqueInsertEdgeSet live adj

def cakeExtendCliqueSetReference : List Nat → List Nat →
    CakeNodeMap (Std.TreeSet Nat) →
    CakeNodeMap (Std.TreeSet Nat) × List Nat
  | [], cli, adj => (adj, cli)
  | x :: xs, cli, adj =>
      if cli.contains x then cakeExtendCliqueSetReference xs cli adj
      else cakeExtendCliqueSetReference xs (x :: cli) (cakeListInsertEdgeSet x cli adj)
termination_by new _ _ => sizeOf new
decreasing_by all_goals decreasing_trivial

def cakeMkGraphSet (ta : Nat → Nat) : WordClashTree → List Nat →
    CakeNodeMap (Std.TreeSet Nat) →
    CakeNodeMap (Std.TreeSet Nat) × List Nat
  | .delta writes reads, liveout, adj =>
      let wta := writes.map ta
      let rta := reads.map ta
      let (adj1, live) := cakeExtendCliqueSet wta liveout adj
      cakeExtendCliqueSet rta (live.filter (fun x => !wta.contains x)) adj1
  | .set names, _liveout, adj =>
      let live := (NumSet.fromAList names).map ta
      (cakeCliqueInsertEdgeSetFast live adj, live)
  | .branch topt t1 t2, liveout, adj =>
      let (adj1, t1Live) := cakeMkGraphSet ta t1 liveout adj
      let (adj2, t2Live) := cakeMkGraphSet ta t2 liveout adj1
      match topt with
      | none => cakeExtendCliqueSet t1Live t2Live adj2
      | some t =>
          let live := (NumSet.fromAList t).map ta
          (cakeCliqueInsertEdgeSetFast live adj2, live)
  | .seq t1 t2, liveout, adj =>
      let (adj1, live) := cakeMkGraphSet ta t2 liveout adj
      cakeMkGraphSet ta t1 live adj1
termination_by tree _ _ => sizeOf tree
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def cakeExtendGraphSet (ta : Nat → Nat) : List (Nat × Nat) →
    CakeNodeMap (Std.TreeSet Nat) → CakeNodeMap (Std.TreeSet Nat)
  | [], adj => adj
  | (x, y) :: rest, adj =>
      cakeExtendGraphSet ta rest (cakeInsertEdgeSet (ta x) (ta y) adj)

/-- `mk_tags` (`reg_allocScript.sml:1159-1176`): tag every node with its
    original variable's role.  Stack-only variables (from `get_stack_only`,
    keyed by original variable name) become `Stemp`, other allocatable
    variables `Atemp`, and physical variables `Fixed` of their register.  The
    original looks up `fa` through `sp_default`, so an unmapped node falls
    back to variable `0`, i.e. `Fixed 0`. -/
def cakeMkTags (n : Nat) (fromAllocator : NatInfoMap Nat) (fs : List Nat) :
    CakeNodeMap CakeNodeTag :=
  /- `fs` is `get_stack_only`'s output, an sptree upstream
     (`reg_allocScript.sml:1159-1176`), and this asks it for membership once
     per node; as a list that was a rescan per node.  Build the membership
     side once.  The tags themselves are unchanged. -/
  let stackOnly := Flapjack.natSetOfList fs
  let sourceIndex := cakeSpDefaultIndex fromAllocator
  (List.range n).foldl (fun tags i =>
      let v := cakeSpDefaultIndexed sourceIndex i
      match v % 4 with
      | 1 => tags.set i (if stackOnly.contains v then .sTemp else .aTemp)
      | 3 => tags.set i .sTemp
      | _ => tags.set i (.fixed (v / 2)))
    (CakeNodeMap.ofSize n)

/-- `init_ra_state` (`reg_allocScript.sml:1241-1250`): the initial allocator
    state for a clash tree. -/
def cakeInitRaStateFromBij (bij : CakeNodeBijection) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) : CakeRaState :=
  let sourceIndex := cakeSpDefaultIndex bij.toAllocator
  let ta := cakeSpDefaultIndexed sourceIndex
  let (adj, _) := cakeMkGraphSet ta tree [] (cakeAdjSetMapOfSize bij.nextNode)
  let adjSets := cakeExtendGraphSet ta forced adj
  let adj := adjSets.mapValues cakeAdjSetList
  let tags := cakeMkTags bij.nextNode bij.fromAllocator fs
  { (CakeRaState.empty bij.nextNode) with
    adjLists := adj,
    adjSets := some adjSets,
    nodeTag := tags }

def cakeInitRaState (tree : WordClashTree) (forced : List (Nat × Nat))
    (fs : List Nat) : CakeRaState :=
  cakeInitRaStateFromBij (cakeMkBij tree) tree forced fs

/-- `is_Fixed` (`reg_allocScript.sml:449-454`): a physical node. -/
def cakeIsFixed (state : CakeRaState) (x : Nat) : Bool :=
  match (state.nodeTag.get x).getD .aTemp with
  | .fixed _ => true
  | _ => false

/-- `is_Fixed_k` (`reg_allocScript.sml:501-506`): a physical node within the
    allocatable window `k`. -/
def cakeIsFixedK (state : CakeRaState) (k : Nat) (x : Nat) : Bool :=
  match (state.nodeTag.get x).getD .aTemp with
  | .fixed n => n < k
  | _ => false

/-- `considered_var` (`reg_allocScript.sml:507-512`): allocation temps and
    low physical registers count towards degrees. -/
def cakeConsideredVar (state : CakeRaState) (k : Nat) (v : Nat) : Bool :=
  match state.nodeTag.get v with
  | none => true
  | some .aTemp => true
  | some (.fixed n) => n < k
  | some .sTemp => false

/-- `is_not_coalesced` (`reg_allocScript.sml:320-327`): the node is its own
    coalescing parent. -/
def cakeIsNotCoalesced (state : CakeRaState) (v : Nat) : Bool :=
  (state.coalesced.get v).getD v == v

/-- `split_degree` (`reg_allocScript.sml:330-340`): low-degree (relative to
    `k`) uncoalesced allocation nodes; nodes at or above the dimension stay
    on the worklist side. -/
def cakeSplitDegree (state : CakeRaState) (d k v : Nat) : Bool :=
  if v < d then
    ((state.degrees.get v).getD 0 < k) && cakeIsNotCoalesced state v
  else true

/-- `st_ex_filter`/`st_ex_partition` accumulate by prepending, so the
    results are reversed (`reg_allocScript.sml:158-180`). -/
def filterReversed {α : Type u} (p : α → Bool) (l : List α) : List α :=
  l.foldl (fun acc x => if p x then x :: acc else acc) []

def partitionReversed {α : Type u} (p : α → Bool) (l : List α) : List α × List α :=
  let (tt, ff) := l.partition p
  (tt.reverse, ff.reverse)

/-! `sort` (`Portable.sml:348-361`) is Cake's tail-recursive merge sort.
    `mergesortN_tail` recursively splits at `DIV2`, toggles `negate` at each
    split, and uses an accumulator merge.  Keeping the split and toggle
    explicit is important: with a strict relation, equal-priority entries
    intentionally change order according to the recursion depth. -/
def cakeSort2Tail {α : Type u} (negate : Bool) (ord : α → α → Bool)
    (x y : α) : List α :=
  if ord x y != negate then [x, y] else [y, x]

def cakeSort3Tail {α : Type u} (negate : Bool) (ord : α → α → Bool)
    (x y z : α) : List α :=
  if ord x y != negate then
    if ord y z != negate then [x, y, z]
    else if ord x z != negate then [x, z, y]
    else [z, x, y]
  else if ord y z != negate then
    if ord x z != negate then [y, x, z]
    else [y, z, x]
  else [z, y, x]

def cakeMergeTail {α : Type u} (negate : Bool) (ord : α → α → Bool) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | left, [], acc => left.reverse ++ acc
  | [], right, acc => right.reverse ++ acc
  | leftHead :: leftTail, rightHead :: rightTail, acc =>
      if ord leftHead rightHead != negate then
        cakeMergeTail negate ord leftTail (rightHead :: rightTail)
          (leftHead :: acc)
      else
        cakeMergeTail negate ord (leftHead :: leftTail) rightTail
          (rightHead :: acc)
  termination_by left right _acc => left.length + right.length
  decreasing_by all_goals simp +arith

def cakeSortN {α : Type u} (negate : Bool) (ord : α → α → Bool) :
    Nat → List α → List α
  | 0, _ => []
  | 1, [] => []
  | 1, x :: _ => [x]
  | 2, [] => []
  | 2, [x] => [x]
  | 2, x :: y :: _ => cakeSort2Tail negate ord x y
  | 3, [] => []
  | 3, [x] => [x]
  | 3, [x, y] => cakeSort2Tail negate ord x y
  | 3, x :: y :: z :: _ => cakeSort3Tail negate ord x y z
  | n + 4, items =>
      let len1 := (n + 4) / 2
      let nextNegate := !negate
      cakeMergeTail nextNegate ord
        (cakeSortN nextNegate ord ((n + 4) / 2) items)
        (cakeSortN nextNegate ord (n + 4 - len1) (items.drop len1)) []
  termination_by n _items => n
  decreasing_by
    all_goals
      have hn : 0 < n + 4 := by omega
      have hdiv : (n + 4) / 2 < n + 4 := Nat.div_lt_self hn (by decide)
      omega

def cakeSort {α : Type u} (ord : α → α → Bool) (items : List α) : List α :=
  cakeSortN false ord items.length items

/-! `sort_moves` (`reg_allocScript.sml:343-346`) uses Cake's generic `sort`
    with a strict priority comparison. -/
def cakeSortMoves (moves : List (Nat × (Nat × Nat))) :
    List (Nat × (Nat × Nat)) :=
  cakeSort (fun a b => a.1 > b.1) moves

/-- `move_related_sub`: a node flagged by `reset_move_related`. -/
def cakeMoveRelatedSub (state : CakeRaState) (v : Nat) : Bool :=
  (state.moveRelated.get v).getD false

/-- `init_alloc1_heu` (`reg_allocScript.sml:1262-1286`): degrees count only
    considered neighbours, every node becomes its own coalescing parent, the
    move worklist is sorted by priority, `reset_move_related`
    (`:708-725`) clears the flags and re-marks non-fixed move endpoints, and
    the allocation temps split into spill / freeze / simplify worklists. -/
def cakeInitAlloc1Heu (moves : List (Nat × (Nat × Nat))) (k : Nat)
    (state : CakeRaState) : Nat × CakeRaState :=
  let dim := state.dim
  let ds := List.range dim
  /- The allocatable-node collection and the three disjoint initialisations
     share the same Cake node traversal.  Prepending matches
     `filterReversed`; tags are immutable during this pass. -/
  let (allocs, initialized) :=
    ds.foldl (fun (acc : List Nat × CakeRaState) i =>
        let (allocs, st) := acc
        let neighbours := (st.adjLists.get i).getD []
        let fills := neighbours.filter (cakeConsideredVar st k)
        let allocs := if (state.nodeTag.get i).getD .aTemp == .aTemp then
          i :: allocs else allocs
        (allocs, { st with
          degrees := st.degrees.set i fills.length
          coalesced := st.coalesced.set i i
          moveRelated := st.moveRelated.set i false }))
      ([], state)
  let withMoves :=
    { initialized with
      availMovesWl := cakeSortMoves moves }
  let withRelated :=
    moves.foldl (fun st move =>
        let x := move.2.1
        let y := move.2.2
        let fixedX := cakeIsFixed st x
        let fixedY := cakeIsFixed st y
        let st := { st with moveRelated := st.moveRelated.set x (!fixedX) }
        { st with moveRelated := st.moveRelated.set y (!fixedY) })
      withMoves
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
  let d := (state.degrees.get v).getD 0
  { state with degrees := state.degrees.set v (d - 1) }

/-- `dec_degree`: decrement the degrees of all nodes adjacent to `x`. -/
def cakeDecDegree (x : Nat) (state : CakeRaState) : CakeRaState :=
  if x < state.dim then
    (cakeAdjSub state.adjLists x).foldl (fun s v => cakeDecDeg v s) state
  else
    state

/-- `push_stack` (`reg_allocScript.sml:300-307`). -/
def cakePushStack (x : Nat) (state : CakeRaState) : CakeRaState :=
  { state with
    degrees := state.degrees.set x 0,
    moveRelated := state.moveRelated.set x false,
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
  let (revived, unavail) := partitionReversed (fun m =>
      vs.any (fun v => cakeAdjMem state m.2.1 v) ||
        vs.any (fun v => cakeAdjMem state m.2.2 v))
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
  let old := (state.degrees.get n).getD 0
  { state with degrees := state.degrees.set n (old + d) }

/-- `deg_or_inf` (`reg_allocScript.sml:524-531`). -/
def cakeDegOrInf (state : CakeRaState) (k x : Nat) : Nat :=
  if cakeIsFixedK state k x then k else (state.degrees.get x).getD 0

/-- `bg_ok` (`reg_allocScript.sml:533-562`): the George coalescing test,
    returning the (case1, case2) adjacency splits on success. -/
def cakeBgOk (k x y : Nat) (state : CakeRaState) : Option (List Nat × List Nat) :=
  let adjX := cakeAdjSub state.adjLists x
  let adjY := cakeAdjSub state.adjLists y
  let (case1, case2) := partitionReversed (fun v => cakeAdjMem state v x) adjY
  let case1 := filterReversed (fun v => cakeConsideredVar state k v) case1
  let case2 := filterReversed (fun v => cakeConsideredVar state k v) case2
  let case2High := case2.countP (fun v => cakeDegOrInf state k v >= k)
  if case2High = 0 then
    some (case1, case2)
  else
    let case3 := filterReversed (fun v => cakeConsideredVar state k v)
      (adjX.filter (fun v => !cakeAdjMem state v y))
    let c1 := case1.countP (fun v => cakeDegOrInf state (k + 1) v - 1 >= k)
    let c2 := case2High
    let c3 := case3.countP (fun v => cakeDegOrInf state k v >= k)
    if c1 + c2 + c3 < k then some (case1, case2) else none

/-- `consistency_ok` (`reg_allocScript.sml:568-586`). -/
def cakeConsistencyOk (state : CakeRaState) (x y : Nat) : Bool :=
  x != y && !cakeAdjMem state x y &&
    (cakeIsFixed state x || (state.moveRelated.get x).getD false) &&
    (cakeIsFixed state y || (state.moveRelated.get y).getD false) &&
    !(cakeIsFixed state x && cakeIsFixed state y)

/-- `do_coalesce_real` (`reg_allocScript.sml:458-471`). -/
def cakeDoCoalesceReal (x y : Nat) (case1 case2 : List Nat)
    (state : CakeRaState) : CakeRaState :=
  let state := { state with coalesced := state.coalesced.set y x }
  let state := if !cakeIsFixed state x then
    cakeIncDeg x case2.length state else state
  let state := { state with
    adjLists := cakeListInsertEdge x case2 state.adjLists
    adjSets := state.adjSets.map (fun adj => cakeListInsertEdgeSet x case2 adj) }
  let state := case1.foldl (fun s v => cakeDecDeg v s) state
  cakePushStack y state

/-- `coalesce_parent` (`reg_allocScript.sml:592-612`) with path
    compression. -/
def cakeCoalesceParent : Nat → CakeRaState → Nat × CakeRaState
  | x, state =>
      let xt := (state.coalesced.get x).getD x
      if cakeIsFixed state xt then (xt, state)
      else if _h : x <= xt then (x, state)
      else
        let (anc, state) := cakeCoalesceParent xt state
        (anc, { state with coalesced := state.coalesced.set x anc })
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
  if (state.degrees.get x).getD 0 < k then state
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
  /- `cakeMapUpdate` replaces the binding of an existing key in place, so
     folding `false` over every dimension is observationally the fresh map
     `(List.range dim).map (fun v => (v, false))`: every lookup of a node
     key finds `false`, and node keys are all below `dim`.  Building the
     map directly keeps the reset linear — the fold performed one linear
     `cakeMapUpdate` per dimension, i.e. O(dim²) per call, which dominated
     allocation on large functions (the reset runs on every prefreeze
     step of the iterative coalescing loop). -/
  let cleared : CakeNodeMap Bool :=
    { slots := Array.replicate state.dim (some false) }
  let updated := moves.foldl (fun m move =>
      let mx := !cakeIsFixed state move.2.1
      let my := !cakeIsFixed state move.2.2
      (m.set move.2.1 mx).set move.2.2 my)
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
def cakeStExListMinCost (degrees : CakeNodeMap Nat) (scost : CakeNodeMap Nat) :
    List Nat → Nat → Nat → Nat → List Nat → Nat × List Nat
  | [], _, k, _, acc => (k, acc)
  | x :: xs, d, k, v, acc =>
      if x < d then
        let xv := (degrees.get x).getD 0
        let cost := cakeSafeDiv ((scost.get x).getD 0) xv
        if v > cost then
          cakeStExListMinCost degrees scost xs d x cost (k :: acc)
        else cakeStExListMinCost degrees scost xs d k v (x :: acc)
      else cakeStExListMinCost degrees scost xs d k v acc
termination_by l _ _ _ _ => sizeOf l
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `st_ex_list_MAX_deg` (`reg_allocScript.sml:792-808`). -/
def cakeStExListMaxDeg (degrees : CakeNodeMap Nat) :
    List Nat → Nat → Nat → Nat → List Nat → Nat × List Nat
  | [], _, k, _, acc => (k, acc)
  | x :: xs, d, k, v, acc =>
      if x < d then
        let xv := (degrees.get x).getD 0
        if v < xv then cakeStExListMaxDeg degrees xs d x xv (k :: acc)
        else cakeStExListMaxDeg degrees xs d k v (x :: acc)
      else cakeStExListMaxDeg degrees xs d k v acc
termination_by l _ _ _ _ => sizeOf l
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `do_spill` (`reg_allocScript.sml:810-830`). -/
def cakeDoSpill (scost : Option (CakeNodeMap Nat)) (k : Nat)
    (state : CakeRaState) : Bool × CakeRaState :=
  match state.spillWl with
  | [] => (false, state)
  | x :: xs =>
      let xv := (state.degrees.get x).getD 0
      let (y, ys) := match scost with
        | none => cakeStExListMaxDeg state.degrees xs state.dim x xv []
        | some sc =>
            cakeStExListMinCost state.degrees sc xs state.dim x
              (cakeSafeDiv ((sc.get x).getD 0) xv) []
      let state := cakePushStack y (cakeDecDegree y state)
      (true, cakeUnspill k { state with spillWl := ys })

/-- `do_step` (`reg_allocScript.sml:832-857`): the first successful
    transition wins. -/
def cakeDoStep (scost : Option (CakeNodeMap Nat)) (k : Nat)
    (state : CakeRaState) : Bool × CakeRaState :=
  let (b1, s1) := cakeDoSimplify k state
  if b1 then (true, s1)
  else
    let (b2, s2) := cakeDoCoalesce k s1
    if b2 then (true, s2)
    else
      let (b3, s3) := cakeDoPrefreeze k s2
      if b3 then (true, s3)
      else
        let (b4, s4) := cakeDoFreeze k s3
        if b4 then (true, s4) else cakeDoSpill scost k s4

/-- `rpt_do_step` (`reg_allocScript.sml:860-868`). -/
def cakeRptDoStep (scost : Option (CakeNodeMap Nat)) (k : Nat) :
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
      match state.nodeTag.get v with
      | some (.fixed c) => cakeRemoveColours state vs (ks.filter (· ≠ c))
      | _ => cakeRemoveColours state vs ks

/-- `first_match_col` (`reg_allocScript.sml:994-1004`). -/
def cakeFirstMatchCol (state : CakeRaState) (ks : List Nat) : List Nat → Option Nat
  | [] => none
  | v :: vs =>
      match state.nodeTag.get v with
      | some (.fixed m) => if ks.contains m then some m else cakeFirstMatchCol state ks vs
      | _ => cakeFirstMatchCol state ks vs

/-- `coalesce_root` (`reg_allocScript.sml:1363-1378`): read-only parent
    traversal without path compression. -/
def cakeCoalesceRoot : CakeRaState → Nat → Nat
  | state, x =>
      let xt := (state.coalesced.get x).getD x
      if cakeIsFixed state xt then xt
      else if _h : x <= xt then x
      else cakeCoalesceRoot state xt
termination_by _ x => x
decreasing_by all_goals omega

/-- `moves_to_sp` (`reg_allocScript.sml:1326-1345`): the move-partner
    table consulted by the biased colour preferences. -/
def cakeMovesToSp : List (Nat × (Nat × Nat)) →
    CakeNodeMap (List (Nat × Nat)) → CakeNodeMap (List (Nat × Nat))
  | [], table => table
  | (p, (x, y)) :: rest, table =>
      /- `moves_to_sp` inserts the current move before recursing into the
         tail.  Since `pri_move_insert` prepends, this reverses the source
         order in each partner list.  The y endpoint is inserted first by
         `undir_move_insert`, followed by x. -/
      let table := table.set y ((p, x) :: (table.get y).getD [])
      let table := table.set x ((p, y) :: (table.get x).getD [])
      cakeMovesToSp rest table

/-- `resort_moves` (`reg_allocScript.sml:1347-1350`): sort each partner
    list by descending priority, then drop the priorities. -/
def cakeResortMovesSp (table : CakeNodeMap (List (Nat × Nat))) :
    CakeNodeMap (List Nat) :=
  -- Cake's pairwise merge sort is intentionally not stable: `sort_moves`
  -- selects the right run first for equal priorities.
  table.mapValues (fun partners =>
    (cakeSort (fun a b => a.1 > b.1) partners).map (·.2))

/-- `update_move` (`reg_allocScript.sml:1407-1414`). -/
def cakeUpdateMove (spta : Nat → Nat) (move : Nat × (Nat × Nat)) :
    Nat × (Nat × Nat) :=
  let (p, (x, y)) := move
  let spx := spta x
  let spy := spta y
  if spx <= spy then (p, (spx, spy)) else (p, (spy, spx))

/-- `biased_pref` (`reg_allocScript.sml:1380-1395`). -/
def cakeBiasedPref (state : CakeRaState) (mtable : CakeNodeMap (List Nat))
    (n : Nat) (ks : List Nat) : Option Nat :=
  if n < state.dim then
    let v := cakeCoalesceRoot state n
    let vs := (mtable.get n).getD []
    cakeFirstMatchCol state ks (v :: vs)
  else none

/-- `unbound_colour` (`reg_allocScript.sml:946-960`). -/
def cakeUnboundColour (col : Nat) : List Nat → Nat
  | [] => col
  | x :: xs =>
      if col < x then col
      else if col = x then cakeUnboundColour (col + 1) xs
      else cakeUnboundColour col xs

/-! Cake's `unbound_colour` proof: a sorted forbidden-colour list never
    forces the negative preference below `k` or back onto a forbidden colour. -/
theorem cakeUnboundColour_correct
    (col : Nat) (colours : List Nat)
    (hsorted : List.Pairwise (fun left right : Nat => left ≤ right) colours) :
    col ≤ cakeUnboundColour col colours ∧
      cakeUnboundColour col colours ∉ colours := by
  induction colours generalizing col with
  | nil =>
      simp [cakeUnboundColour]
  | cons head tail ih =>
      simp only [List.pairwise_cons] at hsorted
      by_cases hlt : col < head
      · have hnotHead : col ≠ head := by omega
        have hnotTail : col ∉ tail := by
          intro hmem
          have hheadTail := hsorted.1 col hmem
          omega
        simp [cakeUnboundColour, hlt, hnotHead, hnotTail]
      · by_cases heq : col = head
        · have h := ih (col := col + 1) hsorted.2
          subst col
          have hnotHead : cakeUnboundColour (head + 1) tail ≠ head := by
            intro hsame
            omega
          rw [cakeUnboundColour]
          simp only [Nat.lt_irrefl, ↓reduceIte]
          constructor
          · omega
          · simp only [List.mem_cons, not_or]
            exact ⟨hnotHead, h.2⟩
        · have hheadLe : head ≤ col := Nat.le_of_not_gt hlt
          have h := ih (col := col) hsorted.2
          have hnotHead : cakeUnboundColour col tail ≠ head := by
            intro hsame
            omega
          rw [cakeUnboundColour]
          simp only [hlt, ↓reduceIte, heq]
          exact ⟨h.1, by
            simp only [List.mem_cons, not_or]
            exact ⟨hnotHead, h.2⟩⟩

/-- `neg_first_match_col` (`reg_allocScript.sml:1420-1436`). -/
def cakeNegFirstMatchCol (state : CakeRaState) (k : Nat) (bads : List Nat) :
    List Nat → Option Nat
  | [] => none
  | m :: ms =>
      match state.nodeTag.get m with
      | some (.fixed c) =>
          if bads.contains c || c < k then cakeNegFirstMatchCol state k bads ms
          else some c
      | some _ => cakeNegFirstMatchCol state k bads ms
      | none => none

/-- `neg_biased_pref` (`reg_allocScript.sml:1438-1450`). -/
def cakeNegBiasedPref (state : CakeRaState) (k : Nat)
    (mtable : CakeNodeMap (List Nat)) (n : Nat) (bads : List Nat) : Option Nat :=
  if n < state.dim then
    match mtable.get n with
    | none => none
    | some vs => cakeNegFirstMatchCol state k bads vs
  else none

/-- `tag_col` (`reg_allocScript.sml:941-944`). -/
def cakeTagCol (state : CakeRaState) (v : Nat) : Nat :=
  match state.nodeTag.get v with
  | some (.fixed m) => m
  | _ => 0

/-- `assign_Atemp_tag` (`reg_allocScript.sml:903-927`). -/
def cakeAssignAtempTag (k : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (n : Nat)
    (state : CakeRaState) : CakeRaState :=
  match state.nodeTag.get n with
  | some .aTemp =>
      let ks' := cakeRemoveColours state (cakeAdjSub state.adjLists n) (List.range k)
      match ks' with
      | [] => { state with nodeTag := state.nodeTag.set n .sTemp }
      | c :: _ =>
          match prefs state n ks' with
          | none => { state with nodeTag := state.nodeTag.set n (.fixed c) }
          | some y => { state with nodeTag := state.nodeTag.set n (.fixed y) }
  | _ => state

/-- `assign_Atemps` (`reg_allocScript.sml:923-938`). -/
def cakeAssignAtemps (k : Nat) (ls : List Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat)
    (state : CakeRaState) : CakeRaState :=
  /- Cake's `get_stack` returns the newest-first list built by `push_stack`,
     and `st_ex_FOREACH` consumes that list in its stored order. -/
  let lsF := ls.filter (· < state.dim)
  let state := lsF.foldl (fun s n => cakeAssignAtempTag k prefs n s) state
  (List.range state.dim).foldl (fun s n => cakeAssignAtempTag k prefs n s) state

/-- `assign_Stemp_tag` (`reg_allocScript.sml:962-982`). -/
def cakeAssignStempTag (k : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (n : Nat)
    (state : CakeRaState) : CakeRaState :=
  match state.nodeTag.get n with
  | some .sTemp =>
      let bads := cakeSort (fun a b => a <= b)
        ((cakeAdjSub state.adjLists n).map (fun v => cakeTagCol state v))
      match prefs state n bads with
      | none =>
          { state with
            nodeTag := state.nodeTag.set n (.fixed (cakeUnboundColour k bads)) }
      | some y =>
          { state with nodeTag := state.nodeTag.set n (.fixed y) }
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
  /- `toAllocator` is a bijection, so its sorted keys are unique.  Cake's
     update loop therefore appends each freshly seen key; mapping the sorted
     entries directly preserves the observable association-list order while
     avoiding a quadratic rebuild of the result. -/
  (toAllocator.mergeSort (fun a b => a.1 < b.1)).map
    (fun entry => (entry.1, cakeTagCol state entry.2))

/-- `full_consistency_ok` (`reg_allocScript.sml:1385+`). -/
def cakeTagIsAtemp (state : CakeRaState) (x : Nat) : Bool :=
  match state.nodeTag.get x with
  | some .aTemp => true
  | _ => false

def cakeFullConsistencyOk (state : CakeRaState) (k : Nat) (x y : Nat) : Bool :=
  let tagX := state.nodeTag.get x
  let tagY := state.nodeTag.get y
  let fixedX := match tagX with
    | some (.fixed n) => n < k
    | _ => false
  let fixedY := match tagY with
    | some (.fixed n) => n < k
    | _ => false
  let eligibleX := fixedX || match tagX with
    | some .aTemp => true
    | _ => false
  let eligibleY := fixedY || match tagY with
    | some .aTemp => true
    | _ => false
  /- Keep the cheap domain/tag checks before the indexed adjacency lookup.
     This is the same left-to-right Boolean contract as Cake's conjunction,
     but avoids touching the graph for ineligible move endpoints. -/
  x != y && x < state.dim && y < state.dim &&
    eligibleX && eligibleY && !(fixedX && fixedY) &&
    !cakeAdjMem state x y

/-- A lookup-only index for the source-variable side of `mk_bij`.

    Cake's `toAllocator` association list is a bijection with unique source
    keys.  The list remains the canonical ordered representation everywhere
    observable; this index is used only for the repeated `update_move` lookups
    in the allocator hot path. -/
def cakeAllocatorIndex (toAllocator : NatInfoMap Nat) : Std.HashMap Nat Nat :=
  toAllocator.foldl (fun index entry =>
    match index[entry.1]? with
    | some _ => index
    | none => index.insert entry.1 entry.2) {}

def cakeAllocatorIndexLookup (index : Std.HashMap Nat Nat) (name : Nat) : Nat :=
  cakeSpDefaultIndexed index name

/-- The allocator flavour, mirroring `algorithm` in the original. -/
inductive CakeAlgorithm : Type
  | simple : CakeAlgorithm
  | irc : CakeAlgorithm

/-- `do_reg_alloc` (`reg_allocScript.sml:1452-1470`): the complete IRC
    colouring pipeline over a clash tree, producing the var → colour
    table. -/
def cakeDoRegAllocFromState (alg : CakeAlgorithm) (scost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat)))
    (bij : CakeNodeBijection) (state : CakeRaState) : Option (NatInfoMap Nat) :=
  let sourceIndex := cakeAllocatorIndex bij.toAllocator
  let spta := fun name => cakeAllocatorIndexLookup sourceIndex name
  let moves0 := moves.map (cakeUpdateMove spta)
  let movesF := filterReversed (fun m => cakeFullConsistencyOk state k m.2.1 m.2.2) moves0
  let selMoves := match alg with
    | .simple => []
    | .irc => movesF
  let (l, s0) := cakeInitAlloc1Heu selMoves k state
  let s1 := cakeRptDoStep scost k l s0
  let ls := s1.stack
  let mvs := cakeResortMovesSp (cakeMovesToSp moves0 (CakeNodeMap.ofSize bij.nextNode))
  let state := cakeAssignAtemps k ls (fun s n ks => cakeBiasedPref s mvs n ks) s1
  let state := cakeAssignStemps k (fun s n bads => cakeNegBiasedPref s k mvs n bads) state
  some (cakeExtractColor state bij.toAllocator)

def cakeDoRegAlloc (alg : CakeAlgorithm) (scost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) : Option (NatInfoMap Nat) :=
  let bij := cakeMkBij tree
  let state := cakeInitRaStateFromBij bij tree forced fs
  cakeDoRegAllocFromState alg scost k moves bij state

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

theorem cakeColourLocation_register_boundary
    (k f register : Nat) (hregister : register < k) :
    cakeColourLocation k f (2 * register) = .register register := by
  simp [cakeColourLocation, hregister]

theorem cakeColourLocation_stack_boundary
    (k f register : Nat) (hregister : k ≤ register) :
    cakeColourLocation k f (2 * register) =
      .stack (f - 1 - (register - k)) := by
  simp [cakeColourLocation, hregister]

/-- A Cake stack colour whose spill index fits the `f`-word frame is assigned
    a concrete slot strictly below that frame, as `format_var` requires. -/
theorem cakeColourLocation_stack_slot_lt_frame
    (k f register : Nat) (hregister : k ≤ register)
    (hslot : register - k < f) :
    ∃ slot, cakeColourLocation k f (2 * register) = .stack slot ∧ slot < f := by
  refine ⟨f - 1 - (register - k),
    cakeColourLocation_stack_boundary k f register hregister, ?_⟩
  omega

def cakeColourFrameSlots (k : Nat) (parameters : List Nat)
    (program : WordProg α) (colouring : NatInfoMap Nat) : Nat × Nat :=
  let colour := CakeAlloc.totalColour colouring
  let coloured := wordApplyColour colour program
  let maxVar := wordProgCakeMaxVar coloured
  let stackArgs := parameters.length - k
  let f' := max ((maxVar / 2 + 1) - k) stackArgs
  (f', if f' = 0 then 0 else f' + 1)

/- Cake's `compile_prog` takes the argument-area floor when it dominates the
   coloured program's spill demand.  Keep this branch kernel-checked beside
   the allocator adapter: it is the frame equation used by the RISC-V
   Word-to-Stack boundary, not a heuristic reconstruction. -/
theorem cakeColourFrameSlots_arg_area_dominates
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat)
    (hdom : (wordProgCakeMaxVar
        (wordApplyColour (CakeAlloc.totalColour colouring) program) / 2 + 1) - k ≤
      parameters.length - k) :
    (cakeColourFrameSlots k parameters program colouring).1 =
      parameters.length - k := by
  simp [cakeColourFrameSlots, hdom]

/- The other `compile_prog` branch is spill-dominant: the coloured program's
   computed occupancy wins the same Cake `MAX` rather than being replaced by
   the formal argument area. -/
theorem cakeColourFrameSlots_spill_dominates
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat)
    (hdom : parameters.length - k ≤
      (wordProgCakeMaxVar
        (wordApplyColour (CakeAlloc.totalColour colouring) program) / 2 + 1) - k) :
    (cakeColourFrameSlots k parameters program colouring).1 =
      (wordProgCakeMaxVar
        (wordApplyColour (CakeAlloc.totalColour colouring) program) / 2 + 1) - k := by
  simp [cakeColourFrameSlots, hdom]

def cakeColourWordSpillState (k : Nat) (parameters : List Nat)
    (program : WordProg α) (colouring : NatInfoMap Nat) : WordSpillState :=
  let colour := CakeAlloc.totalColour colouring
  let (_, f) := cakeColourFrameSlots k parameters program colouring
  let names := (parameters ++ wordProgVariables program).eraseDups
  let locations := names.map (fun name =>
    (name, cakeColourLocation k f (colour name)))
  { locations, nextSpill := if f = 0 then 0 else f - 1 }

/-- Cake's coloured spill cursor is always contained in the frame size emitted
    by `compile_prog`: an empty frame has no cursor, and a nonempty `f`-word
    frame exposes spill slots below its bitmap word. -/
theorem cakeColourWordSpillState_nextSpill_le_frame
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat) :
    (cakeColourWordSpillState k parameters program colouring).nextSpill ≤
      (cakeColourFrameSlots k parameters program colouring).2 := by
  simp [cakeColourWordSpillState]
  split <;> omega

/-- The production Cake allocator adapter retains exactly the `f'` spill
    occupancy from `compile_prog`, including the zero-occupancy case. -/
theorem cakeColourWordSpillState_nextSpill_eq_occupancy
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat) :
    (cakeColourWordSpillState k parameters program colouring).nextSpill =
      (cakeColourFrameSlots k parameters program colouring).1 := by
  simp [cakeColourWordSpillState, cakeColourFrameSlots]
  split <;> omega

/- Cake's `format_var` maps each spill index below the allocator cursor to a
   concrete slot in the frame.  Keep this combined invariant at the adapter
   boundary so callers do not have to separately reconstruct the occupancy
   bound and the location equation. -/
theorem cakeColourWordSpillState_allocated_stack_slot_lt_frame
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat) (register : Nat)
    (hregister : k ≤ register)
    (hslot : register - k <
      (cakeColourWordSpillState k parameters program colouring).nextSpill) :
    ∃ slot, cakeColourLocation k
        (cakeColourFrameSlots k parameters program colouring).2
        (2 * register) = .stack slot ∧
      slot < (cakeColourFrameSlots k parameters program colouring).2 := by
  have hframe := cakeColourWordSpillState_nextSpill_le_frame
    k parameters program colouring
  exact cakeColourLocation_stack_slot_lt_frame
    k (cakeColourFrameSlots k parameters program colouring).2 register
    hregister (by omega)

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
  /- `word_alloc` passes this source-keyed sptree directly to `reg_alloc`.
     Keep those keys intact; `CakeNodeMap` stores keys outside the allocator
     array when necessary, matching `lookup_any` in `st_ex_list_MIN_cost`. -/
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced fs
  match cakeDoRegAllocFromState .irc scost k moves bij initialState with
  | none => none
  | some colouring =>
      some (state, renamedParameters, ssaProgram,
        cakeColourWordSpillState k parameters ssaProgram colouring)

/-! `get_prefs` from the original allocator driver: the move preferences fed
    to IRC (`word_allocScript.sml:1203-1215` via `get_heuristics_def`). -/
def cakeGetPrefs {α : Type u} [OfNat α 0] [OfNat α 1] :
    WordProg α → List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat))
  | .move priority moves, acc =>
      moves.map (fun move => (priority, (move.1, move.2))) ++ acc
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
  /- Keep the source-keyed spill table intact, as `word_alloc` passes it
     directly to `reg_alloc`; out-of-range keys live in `CakeNodeMap.outside`. -/
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced fs
  match cakeDoRegAllocFromState .irc scost k moves bij initialState with
  | none => 0
  | some colouring =>
      let colour := CakeAlloc.totalColour colouring
      let coloured := wordApplyColour colour ssaProgram
      let maxVar := wordProgCakeMaxVar coloured
      let stackArgs := parameters.length - k
      max ((maxVar / 2 + 1) - k) stackArgs

end Flapjack.RiscV.CakeRegAlloc
