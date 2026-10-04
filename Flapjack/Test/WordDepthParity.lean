import Flapjack.Compiler.Backend.WordDepth

/-! Kernel replays of twelve fresh original HOL EVAL rows in word_depth_probe.out.
Lookup misses and Unknown retain NONE; nested calls retain all frame additions. -/

namespace Flapjack.Test.WordDepthParity

open Flapjack.Compiler.Backend.WordDepth

/-- Exact frame map used by the original probe rows (`insert 1 10 (insert 2 20 LN)`). -/
private def fs10 : Flapjack.Spt Nat :=
  Flapjack.sptInsert 1 10 (Flapjack.sptInsert 2 20 Flapjack.Spt.ln)

/-- Direct replay of the original `max_depth` clauses. -/
def wordDepthGuard : Bool :=
  -- leaf
  maxDepth Flapjack.Spt.ln .leaf == some 0 &&
  -- unknown
  maxDepth Flapjack.Spt.ln .unknown == none &&
  -- const_leaf
  maxDepth Flapjack.Spt.ln (.const 5 .leaf) == some 5 &&
  -- nested_const
  maxDepth Flapjack.Spt.ln (.const 3 (.const 4 .leaf)) == some 7 &&
  -- branch_max
  maxDepth Flapjack.Spt.ln (.branch (.const 3 .leaf) (.const 5 .leaf)) == some 5 &&
  -- branch_unknown
  maxDepth Flapjack.Spt.ln (.branch (.const 3 .leaf) .unknown) == none &&
  -- call_hit
  maxDepth fs10 (.call 1 .leaf) == some 10 &&
  -- call_miss
  maxDepth fs10 (.call 7 .leaf) == none &&
  -- call_hit_nested
  maxDepth fs10 (.call 1 (.const 4 .leaf)) == some 14 &&
  -- deep_calls
  maxDepth fs10 (.call 1 (.call 2 (.const 3 .leaf))) == some 33 &&
  -- branch_call
  maxDepth fs10 (.branch (.call 1 .leaf) (.const 2 .leaf)) == some 10 &&
  -- unknown_deep
  maxDepth fs10 (.branch .unknown (.call 1 (.const 9 .leaf))) == none

#guard wordDepthGuard

/-- Kernel-checked replay of the `max_depth` rows. -/
theorem wordDepthGuard_proof : wordDepthGuard = true := by
  simp [wordDepthGuard, maxDepth, optionMap₂, fs10, Flapjack.sptLookup,
    Flapjack.sptInsert]

/-! ## `mk_Branch` / `call_graph` / `full_call_graph` / `max_depth_graphs` replay

The original-HOL oracle for these definitions is
`scripts/hol-probes/word_depth_graph_probeScript.sml`; its captured
`word_depth_graph_probe.out` records the `mk_Branch`/`call_graph`/`full_call_graph`/
`max_depth_graphs` rows (`mb_*`, `cg_*`, `fcg_*`, `mdg_*`). The clauses below
replay each captured row kernel-checked over concrete small programs on the
exact `CallTree` / `WordLangProgHOL` / `Spt` carriers. The captured rows with dynamic
`dest`/lookup-miss/short-circuit/guard behaviour and the returning-call and
handler cases that the `.out` exercises through the `Call` constructor are all
covered. -/

/-- Frame-size map `{2 ↦ 5}` for the replay. -/
private def gFrame2 : Flapjack.Spt Nat := Flapjack.sptInsert 2 5 Flapjack.Spt.ln

/-- Frame-size map `{1 ↦ 4}` for the recursive replay. -/
private def gFrameSelf : Flapjack.Spt Nat := Flapjack.sptInsert 1 4 Flapjack.Spt.ln

/-- Empty cut set pair, the exact `WordLangCutsetsHOL` carrier. -/
private def gCuts : Flapjack.WordLangCutsetsHOL := (Flapjack.Spt.ln, Flapjack.Spt.ln)

/-- Replay word type. -/
private abbrev W8 := BitVec 8

/-- Immediate-return program, the body used by the lookup-hit rows. -/
private def pSkip : Flapjack.WordLangProgHOL W8 := .skip

/-- One-entry code map `{2 ↦ (0, Skip)}`. -/
private def funsHit : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 2 (0, pSkip) Flapjack.Spt.ln

/-- One-entry code map `{1 ↦ (0, Call NONE (SOME 1) [] NONE)}` for the
    tail-recursive replay. -/
private def funsTailSelf : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call none (some 1) [] none : Flapjack.WordLangProgHOL W8))
    Flapjack.Spt.ln

/-- One-entry code map for the returning-call replay
    `{1 ↦ (0, Call (SOME (nil, cuts, Skip, 0, 0)) (SOME 1) [] NONE)}`. -/
private def funsRetSelf : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call (some ([], gCuts, pSkip, 0, 0)) (some 1) [] none :
      Flapjack.WordLangProgHOL W8))
    Flapjack.Spt.ln

/-- Two-entry mutual tail-recursive code map
    `{1 ↦ Call NONE (SOME 2) [] NONE, 2 ↦ Call NONE (SOME 1) [] NONE}`. -/
private def funsMutual : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 1
    (0, (Flapjack.WordLangProgHOL.call none (some 2) [] none : Flapjack.WordLangProgHOL W8))
    (Flapjack.sptInsert 2
      (0, (Flapjack.WordLangProgHOL.call none (some 1) [] none : Flapjack.WordLangProgHOL W8))
      Flapjack.Spt.ln)

/-- Kernel-checked replay of the `mk_Branch` / `call_graph` /
    `full_call_graph` / `max_depth_graphs` clauses over concrete small
    programs: the `mk_Branch` absorptions, the `call_graph` structural cases,
    the `Call` `dest`/`lookup`/short-circuit/guard/return/handler cases, the
    `full_call_graph` hit/miss and tail- and non-tail-recursive programs, and the
    `max_depth_graphs` empty/frame-hit/frame-miss/recursive rows. -/
def wordDepthGraphGuard : Bool :=
  -- mk_Branch: identity, Leaf absorption on both sides, Unknown absorption on
  -- both sides, and the structural Branch case.
  decide (mkBranch (.leaf : CallTree) .leaf = .leaf) &&
  decide (mkBranch (.unknown : CallTree) .unknown = .unknown) &&
  decide (mkBranch (.leaf : CallTree) (.const 1 .leaf) = .const 1 .leaf) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) .leaf = .const 1 .leaf) &&
  decide (mkBranch (.unknown : CallTree) (.const 1 .leaf) = .unknown) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) .unknown = .unknown) &&
  decide (mkBranch ((.const 1 .leaf) : CallTree) (.const 2 .leaf) =
    .branch (.const 1 .leaf) (.const 2 .leaf)) &&
  -- call_graph: default Leaf, Seq of leaves, Seq with Alloc, Alloc, Install,
  -- MustTerminate, Loop, and If.
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.skip : Flapjack.WordLangProgHOL W8) = (.leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.seq .skip .skip : Flapjack.WordLangProgHOL W8) = (.leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.seq (.alloc 7 gCuts) .skip : Flapjack.WordLangProgHOL W8) = (.call 5 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.alloc 7 gCuts : Flapjack.WordLangProgHOL W8) = (.call 5 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      5 [] 0 (.install 0 0 0 0 gCuts : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.mustTerminate (.alloc 7 gCuts) : Flapjack.WordLangProgHOL W8) = (.call 3 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.loop Flapjack.Spt.ln (.alloc 7 gCuts) Flapjack.Spt.ln : Flapjack.WordLangProgHOL W8) =
    (.call 3 .leaf : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      3 [] 0 (.ite .equal 0 (.reg 0) (.alloc 7 gCuts) .skip : Flapjack.WordLangProgHOL W8) =
    (.call 3 .leaf : CallTree)) &&
  -- call_graph Call cases: dynamic target, tail-call hit, tail-call miss,
  -- short-circuit when the target is already on the stack, guard failure when
  -- the stack list has reached `total`, and the returning-call handler cases.
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      7 [] 0 (.call none (some 9) [] none : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      7 [] 0 (.call none none [] none : Flapjack.WordLangProgHOL W8) = (.unknown : CallTree)) &&
  decide (callGraph funsHit 7 [] 1 (.call none (some 2) [] none) = (.call 2 .leaf : CallTree)) &&
  decide (callGraph funsHit 7 [2] 1 (.call none (some 2) [] none) = (.leaf : CallTree)) &&
  decide (callGraph funsHit 7 [] 0 (.call none (some 2) [] none) = (.leaf : CallTree)) &&
  decide (callGraph funsHit 1 [] 1 (.call (some ([], gCuts, pSkip, 0, 0)) (some 2) [] none) =
    (.branch (.call 1 (.call 2 .leaf)) (.call 1 .leaf) : CallTree)) &&
  decide (callGraph funsHit 1 [] 1
      (.call (some ([], gCuts, pSkip, 0, 0)) (some 2) [] (some (0, pSkip, 0, 0))) =
    (.branch (.call 1 (.const 3 (.call 2 .leaf))) (.call 1 (.const 3 .leaf)) : CallTree)) &&
  -- full_call_graph: miss, plain hit, tail-recursive and return-recursive
  -- self calls, and mutual tail recursion.
  decide (fullCallGraph 9 (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) =
    (.unknown : CallTree)) &&
  decide (fullCallGraph 2 funsHit = (.branch (.call 2 .leaf) .leaf : CallTree)) &&
  decide (fullCallGraph 1 funsTailSelf = (.branch (.call 1 .leaf) .leaf : CallTree)) &&
  decide (fullCallGraph 1 funsRetSelf =
    (.branch (.call 1 .leaf) (.branch (.call 1 (.call 1 .leaf)) (.call 1 .unknown)) : CallTree)) &&
  decide (fullCallGraph 1 funsMutual = (.branch (.call 1 .leaf) (.call 2 .leaf) : CallTree)) &&
  -- max_depth_graphs: empty list, frame hit, frame miss, whole-code miss, and
  -- a recursive self call whose cycle is cut.
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) = (some 0 : Option Nat)) &&
  decide (maxDepthGraphs gFrame2 [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) funsHit =
    (some 5 : Option Nat)) &&
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) funsHit =
    (none : Option Nat)) &&
  decide (maxDepthGraphs (Flapjack.Spt.ln : Flapjack.Spt Nat) [9] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8)) = (none : Option Nat)) &&
  decide (maxDepthGraphs gFrameSelf [1] [] funsTailSelf funsTailSelf = (some 4 : Option Nat))

/-- Kernel-checked replay of the call-graph rows. -/
theorem wordDepthGraphGuard_proof : wordDepthGraphGuard = true := by
  simp [wordDepthGraphGuard, mkBranch, callGraph, fullCallGraph, maxDepthGraphs, maxDepth,
    optionMap₂, Flapjack.sptLookup, Flapjack.sptInsert, Flapjack.sptDelete,
    Flapjack.sptMkBN, gFrame2, gFrameSelf, funsHit, funsTailSelf,
    funsRetSelf, funsMutual, pSkip, gCuts]

/-- Original generic metadata observations: allFuns is not restricted to Nat. -/
private def boolMetadataCode : Flapjack.Spt (Bool × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 2 (true, pSkip) Flapjack.Spt.ln
private def listMetadataCode : Flapjack.Spt (List Nat × Flapjack.WordLangProgHOL W8) :=
  Flapjack.sptInsert 2 ([3, 4], pSkip) Flapjack.Spt.ln

def metadataSourceRows : Bool :=
  maxDepthGraphs gFrame2 [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      boolMetadataCode == some 5 &&
  maxDepthGraphs gFrame2 [2] []
      (Flapjack.Spt.ln : Flapjack.Spt (Nat × Flapjack.WordLangProgHOL W8))
      listMetadataCode == some 5

#guard metadataSourceRows
#guard wordDepthGraphGuard

theorem metadataSourceRows_proof : metadataSourceRows = true := by
  simp [metadataSourceRows, maxDepthGraphs, callGraph, maxDepth, optionMap₂,
    boolMetadataCode, listMetadataCode, pSkip, gFrame2,
    Flapjack.sptLookup, Flapjack.sptInsert]

end Flapjack.Test.WordDepthParity
