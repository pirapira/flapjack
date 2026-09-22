import Flapjack.CrepToLoop

/-!
# Original-domain parity for `crep_to_loop$compile` cutset threading

The expected cutsets, handler live sets, and control-annotation live sets
come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_to_loop_cutset_probe.out`, sourced from
`cakeml/pancake/crep_to_loopScript.sml` `compile_def`.

The original compiler threads the statement-region live set `l` into call
cutsets, handler continuations, If branches, and While bodies; expression
temporaries are only accumulated inside `compile_exp`, and only a `Dec`
destination temporary is inserted into the continuation's live set.
-/

namespace Flapjack.Test.CrepToLoopCutsetParity

open Flapjack

/-- Probe context: source variable 1 lives in temp 5, function "f" has
    label 64, and the next free temporary is 11. -/
def probeContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [("f", (64, 0))], maxVar := 10,
    target := .rv64i }

def probeLive : List Nat := [5]

/-- CakeML's `num_set` prints in ascending order; normalize the Flapjack
    list-backed live sets the same way before comparing. -/
def canon (live : List Nat) : List Nat :=
  live.foldl (fun acc name => insertNatSorted name acc) []

/-- Collect each call's normal cutset live set and handler live set in
    traversal order.  The original compiler materializes a default
    `(en, Raise en, Skip, l)` handler tuple for handler-less calls;
    `loopCompileProg` passes `none` there instead.  The original's
    word-level `comp` drops that default tuple's live set again, so this
    divergence has no word-level effect; see bead flapjack-pxn.8.5.14.2. -/
def loopCallLivePairs : LoopProg Nat → List (List Nat × List Nat)
  | .call cutset _ _ handler =>
      let normal := match cutset with
        | some (_, live) => live
        | none => []
      let handlerLive := match handler with
        | some (_, _, _, live) => live
        | none => []
      (canon normal, canon handlerLive) :: []
  | .seq first second => loopCallLivePairs first ++ loopCallLivePairs second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopCallLivePairs thenBranch ++ loopCallLivePairs elseBranch
  | .loop _ body _ => loopCallLivePairs body
  | .mark body => loopCallLivePairs body
  | _ => []

/-- Collect the If annotation live sets in traversal order. -/
def loopIteLives : LoopProg Nat → List (List Nat)
  | .seq first second => loopIteLives first ++ loopIteLives second
  | .ite _ _ _ thenBranch elseBranch live =>
      canon live :: (loopIteLives thenBranch ++ loopIteLives elseBranch)
  | .loop _ body _ => loopIteLives body
  | .mark body => loopIteLives body
  | _ => []

/-- Collect the Loop annotation live sets (entry, exit) in traversal
    order. -/
def loopLoopLives : LoopProg Nat → List (List Nat × List Nat)
  | .seq first second => loopLoopLives first ++ loopLoopLives second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopLoopLives thenBranch ++ loopLoopLives elseBranch
  | .loop entry body exit =>
      (canon entry, canon exit) :: loopLoopLives body
  | .mark body => loopLoopLives body
  | _ => []

def constArgsProgram : CrepProg Nat :=
  .call (some ([1], none)) "f" [.const 1, .const 2]

def load32ArgProgram : CrepProg Nat :=
  .call (some ([1], none)) "f" [.load32 (.const 0)]

def decContinuationProgram : CrepProg Nat :=
  .dec 1 (.const 7) (.call (some ([1], none)) "f" [.var 1])

def ifBranchesProgram : CrepProg Nat :=
  .ite (.load32 (.const 0))
    (.call (some ([1], none)) "f" [.const 1])
    (.call (some ([1], none)) "f" [.const 2])

def whileBodyProgram : CrepProg Nat :=
  .while (.load32 (.const 0))
    (.call (some ([1], none)) "f" [.const 1])

def handlerProgram : CrepProg Nat :=
  .call (some ([1], some (3, .skip))) "f" [.const 1]

def constArgsGuard : Bool :=
  loopCallLivePairs (loopCompileProg probeContext probeLive constArgsProgram)
    = [([5], [5])]

def load32ArgGuard : Bool :=
  loopCallLivePairs (loopCompileProg probeContext probeLive load32ArgProgram)
    = [([5], [5])]

def decContinuationGuard : Bool :=
  loopCallLivePairs (loopCompileProg probeContext probeLive decContinuationProgram)
    = [([5, 11], [5, 11])]

def ifBranchesGuard : Bool :=
  let compiled := loopCompileProg probeContext probeLive ifBranchesProgram
  loopCallLivePairs compiled = [([5], [5]), ([5], [5])] &&
    loopIteLives compiled = [[5]]

def whileBodyGuard : Bool :=
  let compiled := loopCompileProg probeContext probeLive whileBodyProgram
  /- Cake's While equation threads the incoming statement-region `l` through
     the loop, its nested If, and the body.  The condition's temporary is not
     added to those annotations. -/
  loopCallLivePairs compiled = [([5], [5])] &&
    loopIteLives compiled = [[5]] &&
    loopLoopLives compiled = [([5], [5])]

def handlerGuard : Bool :=
  loopCallLivePairs (loopCompileProg probeContext probeLive handlerProgram)
    = [([5], [5])]

/-! CakeML's `insert_insert_eq`, `list_insert_SNOC`, `list_insert_append`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:380/:386/:414`) and
    `domain_list_insert`, ported to the Flapjack list-backed live sets. -/

theorem insertNatSorted_idem_fixture :
    insertNatSorted 3 (insertNatSorted 3 [1, 2, 5]) =
      insertNatSorted 3 [1, 2, 5] :=
  insertNatSorted_idem 3 [1, 2, 5]

theorem loopListInsert_snoc_fixture :
    loopListInsert (([1, 2] : List Nat) ++ [3]) [5] =
      insertNatSorted 3 (loopListInsert [1, 2] [5]) :=
  loopListInsert_snoc 3 [1, 2] [5]

theorem loopListInsert_append_fixture :
    loopListInsert (([1] : List Nat) ++ [2, 3]) [5] =
      loopListInsert [2, 3] (loopListInsert [1] [5]) :=
  loopListInsert_append [1] [2, 3] [5]

theorem loopListInsert_mem_fixture :
    (2 : Nat) ∈ loopListInsert [1, 2] [5] :=
  (loopListInsert_mem 2 [1, 2] [5]).mpr (Or.inl (by simp))

theorem insertNatSorted_mem_fixture :
    (3 : Nat) ∈ insertNatSorted 3 [1, 2, 5] ∧ (4 : Nat) ∉ insertNatSorted 3 [1, 2, 5] := by
  constructor
  · exact (insertNatSorted_mem 3 [1, 2, 5] 3).mpr (Or.inl rfl)
  · intro hmem
    rcases (insertNatSorted_mem 3 [1, 2, 5] 4).mp hmem with h | h
    · omega
    · simp at h

theorem insertNatSorted_comm_fixture :
    insertNatSorted 0 (insertNatSorted 2 ([1, 3] : List Nat)) =
      insertNatSorted 2 (insertNatSorted 0 [1, 3]) :=
  insertNatSorted_comm 0 2 [1, 3]

theorem loopListInsert_insertNatSorted_comm_fixture :
    insertNatSorted 4 (loopListInsert [1, 2] ([5] : List Nat)) =
      loopListInsert [1, 2] (insertNatSorted 4 [5]) :=
  loopListInsert_insertNatSorted_comm 4 [1, 2] [5]

def insertCommGuard : Bool :=
  insertNatSorted 0 (insertNatSorted 2 ([1, 3] : List Nat)) ==
      insertNatSorted 2 (insertNatSorted 0 [1, 3]) &&
    insertNatSorted 4 (loopListInsert [1, 2] ([5] : List Nat)) ==
      loopListInsert [1, 2] (insertNatSorted 4 [5])

#eval insertCommGuard
#guard insertCommGuard

def insertSortedGuard : Bool :=
  loopListInsert (([1, 2] : List Nat) ++ [3]) [5] ==
      insertNatSorted 3 (loopListInsert [1, 2] [5]) &&
    loopListInsert (([1] : List Nat) ++ [2, 3]) [5] ==
      loopListInsert [2, 3] (loopListInsert [1] [5]) &&
    insertNatSorted 3 (insertNatSorted 3 [1, 2, 5]) ==
      insertNatSorted 3 [1, 2, 5] &&
    (loopListInsert (([1, 2] : List Nat) ++ [3]) []).all
      (fun x => x == 1 || x == 2 || x == 3)

#eval insertSortedGuard
#guard insertSortedGuard

def parityGuard : Bool :=
  constArgsGuard && load32ArgGuard && decContinuationGuard && ifBranchesGuard &&
    whileBodyGuard && handlerGuard && insertCommGuard

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    constArgsGuard, load32ArgGuard, decContinuationGuard, ifBranchesGuard,
    whileBodyGuard, handlerGuard, insertSortedGuard, insertCommGuard]
  let names := [
    "crep_to_loop cutset const args", "crep_to_loop cutset load32 arg",
    "crep_to_loop dec continuation live", "crep_to_loop if branches live",
    "crep_to_loop while condition live", "crep_to_loop handler live",
    "crep_to_loop list_insert lemmas", "crep_to_loop list_insert commutation"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CrepToLoopCutsetParity
