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

open Flapjack.RiscV.CakeAlloc (mergeStackOnly mergeStackSets removeTempStack)

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

open Flapjack.RiscV.CakeAlloc (getForcedAddCarry getForcedLongMul)

/-- `get_forced` (`word_allocScript.sml:1694-1725`) for the RISC-V target:
    the coalescing constraints forced by multi-result instructions.
    The original's `AddOverflow`/`SubOverflow`/floating-point clauses have
    no counterparts in `WordArith`, so they collapse to the catch-all;
    the ISA test is constant-true because this backend is RISC-V only.
    Traversal is right-to-left like `get_stack_only_aux`: sequences visit
    the second half first, and a call's return continuation is folded
    before its exception handler. -/
def cakeGetForced {α : Type u} :
    WordProg α → List (Nat × Nat) → List (Nat × Nat)
  | .inst (.arith (.longMul r1 _ r3 r4)), acc => getForcedLongMul r1 r3 r4 ++ acc
  | .inst (.arith (.cakeAddCarry r1 _ r3 r4)), acc =>
      getForcedAddCarry r1 r3 r4 ++ acc
  | .inst _, acc => acc
  | .mustTerminate body, acc => cakeGetForced body acc
  | .seq first second, acc => cakeGetForced first (cakeGetForced second acc)
  | .ite _ _ _ thenBranch elseBranch, acc =>
      cakeGetForced thenBranch (cakeGetForced elseBranch acc)
  | .call (some (_, _, returnHandler, _, _)) _ _ handler, acc =>
      match handler with
      | none => cakeGetForced returnHandler acc
      | some (_, handlerBody, _, _) =>
          cakeGetForced handlerBody (cakeGetForced returnHandler acc)
  | .loop _ body _, acc => cakeGetForced body acc
  | _, acc => acc
  termination_by program _acc => sizeOf program
  decreasing_by
    all_goals first
      | sizeOf_list_dec | decreasing_tactic | decreasing_trivial
        <;> simp_arith

end Flapjack.RiscV.CakeRegAlloc
