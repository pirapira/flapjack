import Flapjack.RiscV.Heuristics

/-!
# Spill costs and canonical move priorities

This is the final arithmetic part of CakeML's heuristic allocator boundary.
The source computes spill costs from the five usage counters, canonicalizes
unordered move pairs, groups repeated moves, and then uses the resulting
weighted count as the coalescing priority.
-/

namespace Flapjack

def wordGetSpillCost (counts : WordHeuristicCounts) (isTail : Bool) : Nat :=
  (counts.lhsConst + 2 * counts.lhsReg + 4 * counts.lhsMem +
    2 * counts.rhsReg + 4 * counts.rhsMem) *
    if isTail then 5 else 1

def wordHeuristicSpillCosts (currentFunction : Nat) (program : WordProg α) :
    NatInfoMap Nat :=
  let result := wordHeuristic currentFunction program ([], [])
  result.1.map (fun entry =>
    (entry.1, wordGetSpillCost entry.2 (!result.2.contains entry.1)))

structure WordCanonicalMove where
  count : Nat
  maxPriority : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

/-! Cake's `Portable.sort` is `mergesort_tail`, not a stable insertion sort.
    This generic helper is kept at the heuristic boundary because both
    `word_alloc$canonize_moves` and `reg_alloc$sort_moves` use that relation.
    The recursive DIV2 split and negate toggle are observable for equal keys. -/
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

def cakeSortTail {α : Type u} (ord : α → α → Bool) (items : List α) : List α :=
  cakeSortN false ord items.length items

def wordCanonicalPriorityMove (move : WordMove) : WordMove :=
  if move.left ≤ move.right then move
  else { move with left := move.right, right := move.left }

def wordPriorityMoveBefore (left right : WordMove) : Bool :=
  if left.left = right.left then
    if left.right = right.right then left.priority < right.priority
    else left.right < right.right
  else left.left < right.left

def wordInsertPriorityMove (move : WordMove) : List WordMove → List WordMove
  | [] => [move]
  | head :: moves =>
      if wordPriorityMoveBefore move head then
        move :: head :: moves
      else
        head :: wordInsertPriorityMove move moves

def wordSortPriorityMoves (moves : List WordMove) : List WordMove :=
  cakeSortTail (fun left right => wordPriorityMoveBefore left right) moves

def wordCanonicalizeMovesAux (current : WordMove) (count : Nat) :
    List WordMove → List WordCanonicalMove → List WordCanonicalMove
  | [], result =>
      { count := count, maxPriority := current.priority,
        left := current.left, right := current.right } :: result
  | move :: moves, result =>
      if current.left = move.left && current.right = move.right then
        wordCanonicalizeMovesAux
          { current with priority := max current.priority move.priority }
          (count + 1) moves result
      else
        wordCanonicalizeMovesAux move 1 moves
          ({ count := count, maxPriority := current.priority,
             left := current.left, right := current.right } :: result)

def wordCanonicalizeMoves (moves : List WordMove) : List WordCanonicalMove :=
  match wordSortPriorityMoves (moves.map wordCanonicalPriorityMove) with
  | [] => []
  | move :: moves =>
      wordCanonicalizeMovesAux move 1 moves []

def wordCoalesceMoveCost (spillCosts : NatInfoMap Nat)
    (move : WordCanonicalMove) : WordMove :=
  let leftCost := if (lookupNatInfo move.left spillCosts).isSome then 1 else 0
  let rightCost := if (lookupNatInfo move.right spillCosts).isSome then 1 else 0
  { priority := move.count *
      (10 * (move.maxPriority + 1) + leftCost + rightCost)
    left := move.left
    right := move.right }

/-- `wordHeuristicSpillCosts` over the tree-backed counter state.  The reference
    definition above stays as the specification; this is what the pipeline
    runs, because the association-list state makes the reference cubic in
    function size.  `Flapjack/Test/HeuristicsFastParity.lean` pins the two together,
    including the order of the returned list. -/
def wordHeuristicSpillCostsFast (currentFunction : Nat) (program : WordProg α) :
    NatInfoMap Nat :=
  let result := wordHeuristicFast currentFunction program ({}, {})
  let calls := result.2.seen
  result.1.toNatInfoMap.map (fun entry =>
    (entry.1, wordGetSpillCost entry.2 (!calls.contains entry.1)))

def wordGetHeuristics (algorithm currentFunction : Nat) (program : WordProg α) :
    List WordMove × Option (NatInfoMap Nat) :=
  let moves := wordProgPrioritizedMoves program
  if algorithm % 2 = 1 then
    let spillCosts := wordHeuristicSpillCostsFast currentFunction program
    (wordCanonicalizeMoves moves |>.map (wordCoalesceMoveCost spillCosts),
      some spillCosts)
  else
    (moves, none)

/-! Select the graph allocator at the heuristic mode boundary.  Odd modes
    carry spill costs into the spill worklist; even modes retain the
    unweighted path.  Simple modes do not pass move preferences to coalescing,
    but retain the original move table for the coloring passes. -/
def wordAllocateGraphForHeuristics (algorithm : Nat)
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (moves colourMoves : List WordMove)
    (colours stackStart : Nat)
    (spillCosts : Option (NatInfoMap Nat)) : Option WordGraphAllocation :=
  if algorithm < 2 then
    match spillCosts with
    | none => wordAllocateGraphSimpleWithColourMoves tree forced fixedSources colourMoves colours stackStart
    | some costs =>
        wordAllocateGraphSimpleWithColourMovesAndSpillCosts tree
          forced fixedSources colourMoves colours stackStart costs
  else
    match spillCosts with
    | none =>
        wordAllocateGraphWithPrefreezeMoves tree forced fixedSources
          moves colourMoves colours stackStart
    | some costs =>
        wordAllocateGraphWithPrefreezeMovesAndSpillCosts tree
          forced fixedSources moves colourMoves colours stackStart costs

theorem wordAllocateGraphForHeuristics_sound
    (algorithm : Nat) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves colourMoves : List WordMove) (colours stackStart : Nat)
    (spillCosts : Option (NatInfoMap Nat)) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphForHeuristics algorithm tree forced fixedSources
      moves colourMoves colours stackStart spillCosts = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  by_cases hsimple : algorithm < 2
  · cases spillCosts with
    | none =>
        have hgraph : wordAllocateGraphSimpleWithColourMoves tree forced fixedSources
            colourMoves colours stackStart = some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        exact wordAllocateGraphSimpleWithColourMoves_sound tree
          forced fixedSources colourMoves colours stackStart allocation hgraph
    | some costs =>
        have hgraph : wordAllocateGraphSimpleWithColourMovesAndSpillCosts tree
            forced fixedSources colourMoves colours stackStart costs =
            some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        exact wordAllocateGraphSimpleWithColourMovesAndSpillCosts_sound
          tree forced fixedSources colourMoves colours stackStart costs allocation hgraph
  · cases spillCosts with
    | none =>
        have hgraph : wordAllocateGraphWithPrefreezeMoves tree
            forced fixedSources moves colourMoves colours stackStart =
            some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        exact wordAllocateGraphWithPrefreezeMoves_sound tree
          forced fixedSources moves colourMoves colours stackStart allocation hgraph
    | some costs =>
        have hgraph : wordAllocateGraphWithPrefreezeMovesAndSpillCosts
            tree forced fixedSources moves colourMoves colours stackStart costs =
            some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        exact wordAllocateGraphWithPrefreezeMovesAndSpillCosts_sound
          tree forced fixedSources moves colourMoves colours stackStart costs allocation hgraph

def wordAllocateGraphFunctionWithHeuristics [OfNat α 0] (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let (moves, spillCosts) := wordGetHeuristics algorithm currentFunction renamedProgram
  let colourMoves := wordProgPrioritizedMoves renamedProgram
  let allocation := wordAllocateGraphForHeuristics algorithm tree forced
    (wordStackOnlyUnion fixedSources stackOnly.forced) moves colourMoves colours
    stackStart spillCosts
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

/-! The location-aware StackLang lowering must retain the SSA names.  The
    coloured result above is useful for the register-only semantic boundary,
    but replacing virtual names before consulting `wordGraphLocations` makes
    lookups fail (and can also accidentally hit another virtual name). -/
def wordAllocateGraphFunctionWithHeuristicsRenamed [OfNat α 0] (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let (moves, spillCosts) := wordGetHeuristics algorithm currentFunction renamedProgram
  let colourMoves := wordProgPrioritizedMoves renamedProgram
  let allocation := wordAllocateGraphForHeuristics algorithm tree forced
    (wordStackOnlyUnion fixedSources stackOnly.forced) moves colourMoves colours
    stackStart spillCosts
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

theorem wordAllocateGraphFunctionWithHeuristics_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristics] at halloc
  rcases halloc with ⟨allocationWitness, hgraph, hstate, hparameters, hallocation, hprogram⟩
  subst allocationWitness
  have hsound := wordAllocateGraphForHeuristics_sound algorithm
    ((WordClashTree.set (wordSsaRenameFunction parameters program).2.fst).seq
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
    (wordStackOnlyUnion fixedSources
      (wordStackOnly (wordSsaRenameFunction parameters program).2.snd).forced)
    (wordGetHeuristics algorithm currentFunction
      (wordSsaRenameFunction parameters program).2.snd).1
    (wordProgPrioritizedMoves (wordSsaRenameFunction parameters program).2.snd)
    colours stackStart
    (wordGetHeuristics algorithm currentFunction
      (wordSsaRenameFunction parameters program).2.snd).2
    allocation hgraph
  exact hsound

theorem wordAllocateGraphFunctionWithHeuristicsRenamed_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
      (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristicsRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation'
  have hsound := wordAllocateGraphForHeuristics_sound algorithm
    ((WordClashTree.set (wordSsaRenameFunction parameters program).2.fst).seq
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
    (wordStackOnlyUnion fixedSources
      (wordStackOnly (wordSsaRenameFunction parameters program).2.snd).forced)
    (wordGetHeuristics algorithm currentFunction
      (wordSsaRenameFunction parameters program).2.snd).1
    (wordProgPrioritizedMoves (wordSsaRenameFunction parameters program).2.snd)
    colours stackStart
    (wordGetHeuristics algorithm currentFunction
      (wordSsaRenameFunction parameters program).2.snd).2
    allocation hgraph
  exact hsound


/-! Heuristic allocation over the complete CakeML-shaped SSA function.  The
    formal-entry move is part of the allocated program, so the graph and its
    preferences see the same boundary as the full-SSA spill pipeline. -/
def wordAllocateGraphFunctionWithHeuristicsEntryRenamed [OfNat α 0] (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let (moves, spillCosts) := wordGetHeuristics algorithm currentFunction renamedProgram
  let colourMoves := wordProgPrioritizedMoves renamedProgram
  let allocation := wordAllocateGraphForHeuristics algorithm tree forced
    (wordStackOnlyUnion fixedSources stackOnly.forced) moves colourMoves colours stackStart spillCosts
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

theorem wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristicsEntryRenamed] at halloc
  rcases halloc with ⟨allocation_, hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation_
  have hgraphFull :
      wordAllocateGraphForHeuristics algorithm
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))
        (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources
          (wordStackOnly renamedProgram).forced)
        (wordGetHeuristics algorithm currentFunction renamedProgram).1
        (wordProgPrioritizedMoves renamedProgram) colours stackStart
        (wordGetHeuristics algorithm currentFunction renamedProgram).2 =
        some allocation := by
    simpa [hstate, hparameters, hprogram] using hgraph
  have hsound := wordAllocateGraphForHeuristics_sound algorithm
    ((WordClashTree.set renamedParameters).seq
      (wordClashTree renamedProgram []))
    (wordProgForcedClashes renamedProgram)
    (wordStackOnlyUnion fixedSources
      (wordStackOnly renamedProgram).forced)
    (wordGetHeuristics algorithm currentFunction renamedProgram).1
    (wordProgPrioritizedMoves renamedProgram) colours stackStart
    (wordGetHeuristics algorithm currentFunction renamedProgram).2
    allocation hgraphFull
  simpa [hstate, hparameters, hprogram] using hsound

end Flapjack
