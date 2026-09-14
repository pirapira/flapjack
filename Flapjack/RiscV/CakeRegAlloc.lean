import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.Allocator

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
optional live set, and a `Set` node remaps its fixed list.  The original
`Set` case walks a `num_set` in ascending key order; Flapjack's clash tree
carries the names as a list, so the caller's list order is used verbatim. -/

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

/-- `mk_bij_aux` (`reg_allocScript.sml:1105-1117`). -/
def cakeMkBijAux : WordClashTree → CakeNodeBijection → CakeNodeBijection
  | .delta writes reads, bijection =>
      cakeListRemap writes (cakeListRemap reads bijection)
  | .set names, bijection => cakeListRemap names bijection
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
