import Flapjack.RiscV.Allocator

namespace Flapjack

/-!
The data model used by the CakeML graph-colouring allocator.

The executable spill allocator in Allocator.lean is deliberately small.  This
module ports the next layer of the source development: Fixed/Atemp/Stemp node
tags, the source-variable to graph-node bijection, and the graph builder that
interprets a clash tree as cliques.
-/

inductive WordRegTag where
  | fixed (colour : Nat)
  | atemp
  | stemp
  deriving DecidableEq, Repr

def wordTagColour : WordRegTag → Nat
  | .fixed colour => colour
  | .atemp | .stemp => 0

def wordIsStackVar (name : Nat) : Prop :=
  name % 4 = 3

def wordIsPhysicalVar (name : Nat) : Prop :=
  name % 2 = 0

def wordIsAllocVar (name : Nat) : Prop :=
  name % 4 = 1

def wordTagForSource (fixedSources : List Nat)
    (source : Nat) : WordRegTag :=
  let remainder := source % 4
  if remainder = 1 then
    if source ∈ fixedSources then .stemp else .atemp
  else if remainder = 3 then
    .stemp
  else
    .fixed (source / 2)

def wordMkTags (dimension : Nat) (fixedSources : List Nat)
    (fromNode : NatInfoMap Nat) : NatInfoMap WordRegTag :=
  (List.range dimension).map (fun node =>
    let source := match lookupNatInfo node fromNode with
      | some source => source
      | none => 0
    (node, wordTagForSource fixedSources source))

structure WordRegGraph where
  adjacency : NatInfoMap (List Nat)
  tags : NatInfoMap WordRegTag
  dimension : Nat
  deriving Repr

def wordGraphNeighbours (graph : WordRegGraph) (node : Nat) : List Nat :=
  match lookupNatInfo node graph.adjacency with
  | some neighbours => neighbours
  | none => []

def wordGraphUpdate (node : Nat) (neighbours : List Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  (node, neighbours) :: adjacency.filter (fun entry => entry.1 != node)

def wordGraphInsertNeighbour (node neighbour : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let current := wordGraphNeighbours graph node
  if neighbour ∈ current then
    graph
  else
    { graph with adjacency :=
        wordGraphUpdate node (neighbour :: current) graph.adjacency }

def wordGraphInsertEdge (left right : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let graph := wordGraphInsertNeighbour left right graph
  wordGraphInsertNeighbour right left graph

def wordGraphInsertEdges (node : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | neighbour :: neighbours, graph =>
      wordGraphInsertEdges node neighbours
        (wordGraphInsertEdge node neighbour graph)

def wordGraphExtendClique : List Nat → List Nat → WordRegGraph →
    WordRegGraph × List Nat
  | [], clique, graph => (graph, clique)
  | node :: nodes, clique, graph =>
      if node ∈ clique then
        wordGraphExtendClique nodes clique graph
      else
        wordGraphExtendClique nodes (node :: clique)
          (wordGraphInsertEdges node clique graph)

def wordGraphInsertClique : List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordGraphInsertClique nodes
        (wordGraphInsertEdges node nodes graph)

structure WordBijection where
  toNode : NatInfoMap Nat
  fromNode : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordListRemap : List Nat → WordBijection → WordBijection
  | [], bijection => bijection
  | source :: sources, bijection =>
      match lookupNatInfo source bijection.toNode with
      | some _ => wordListRemap sources bijection
      | none =>
          wordListRemap sources
            { toNode := (source, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, source) :: bijection.fromNode
              next := bijection.next + 1 }

def wordClashTreeBijection : WordClashTree → WordBijection →
    WordBijection
  | .delta writes reads, bijection =>
      wordListRemap (writes ++ reads) bijection
  | .set names, bijection => wordListRemap names bijection
  | .branch branchLive thenBranch elseBranch, bijection =>
      let bijection := wordClashTreeBijection thenBranch bijection
      let bijection := wordClashTreeBijection elseBranch bijection
      match branchLive with
      | none => bijection
      | some names => wordListRemap names bijection
  | .seq first second, bijection =>
      wordClashTreeBijection first
        (wordClashTreeBijection second bijection)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordMkBijection (tree : WordClashTree) : WordBijection :=
  wordClashTreeBijection tree
    { toNode := [], fromNode := [], next := 0 }

def wordBijectionToNode (bijection : WordBijection) (source : Nat) : Nat :=
  match lookupNatInfo source bijection.toNode with
  | some node => node
  | none => bijection.next

structure WordGraphResult where
  graph : WordRegGraph
  liveIn : List Nat
  deriving Repr

def wordMkGraph (toNode : Nat → Nat) : WordClashTree → List Nat →
    WordRegGraph → WordGraphResult
  | .delta writes reads, liveOut, graph =>
      let writes := writes.map toNode
      let reads := reads.map toNode
      let (graph, live) := wordGraphExtendClique writes liveOut graph
      let live := live.filter (fun node => node ∉ writes)
      let (graph, liveIn) := wordGraphExtendClique reads live graph
      { graph := graph, liveIn := liveIn }
  | .set names, _, graph =>
      let names := names.map toNode
      { graph := wordGraphInsertClique names graph, liveIn := names }
  | .branch branchLive thenBranch elseBranch, liveOut, graph =>
      let thenResult := wordMkGraph toNode thenBranch liveOut graph
      let elseResult :=
        wordMkGraph toNode elseBranch liveOut thenResult.graph
      match branchLive with
      | none =>
          let (graph, liveIn) := wordGraphExtendClique
            thenResult.liveIn elseResult.liveIn elseResult.graph
          { graph := graph, liveIn := liveIn }
      | some names =>
          let names := names.map toNode
          { graph := wordGraphInsertClique names elseResult.graph
            liveIn := names }
  | .seq first second, liveOut, graph =>
      let secondResult := wordMkGraph toNode second liveOut graph
      wordMkGraph toNode first secondResult.liveIn secondResult.graph
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordTagFixedColour : WordRegTag → Option Nat
  | .fixed colour => some colour
  | .atemp | .stemp => none

def wordFixedNeighbourColours (nodes : List Nat)
    (tags : NatInfoMap WordRegTag) : List Nat :=
  match nodes with
  | [] => []
  | node :: nodes =>
      let colours := match lookupNatInfo node tags with
        | some tag =>
            match wordTagFixedColour tag with
            | some colour => [colour]
            | none => []
        | none => []
      colours ++ wordFixedNeighbourColours nodes tags

def wordRemoveColours (removed colours : List Nat) : List Nat :=
  match colours with
  | [] => []
  | colour :: colours =>
      if colour ∈ removed then
        wordRemoveColours removed colours
      else
        colour :: wordRemoveColours removed colours

def wordStackColourCandidates (start : Nat) (blocked : List Nat) : List Nat :=
  (List.range (start + blocked.length + 1)).filter
    (fun colour => colour ≥ start)

def wordUnboundColour (start : Nat) (blocked : List Nat) : Nat :=
  match wordFirstAvailable (wordStackColourCandidates start blocked) blocked with
  | some colour => colour
  | none => start

def wordGraphUpdateTag (node : Nat) (tag : WordRegTag)
    (tags : NatInfoMap WordRegTag) : NatInfoMap WordRegTag :=
  (node, tag) :: tags.filter (fun entry => entry.1 != node)

def wordAssignAtempTag (colours : List Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .atemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      match wordFirstAvailable (wordRemoveColours blocked colours) blocked with
      | some colour =>
          { graph with tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      | none =>
          { graph with tags := wordGraphUpdateTag node .stemp graph.tags }
  | some (.fixed _) | some .stemp | none => graph

def wordAssignAtemps (colours : List Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignAtemps colours nodes (wordAssignAtempTag colours node graph)

def wordAssignStempTag (stackStart : Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .stemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      let colour := wordUnboundColour stackStart blocked
      { graph with tags :=
          wordGraphUpdateTag node (.fixed colour) graph.tags }
  | some (.fixed _) | some .atemp | none => graph

def wordAssignStemps (stackStart : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignStemps stackStart nodes
        (wordAssignStempTag stackStart node graph)

def wordColourGraph (dimension colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let nodes := List.range dimension
  let colours := List.range colours
  let graph := wordAssignAtemps colours nodes graph
  wordAssignStemps stackStart nodes graph

def wordGraphTagColour (graph : WordRegGraph) (node : Nat) : Option Nat :=
  match lookupNatInfo node graph.tags with
  | some tag => wordTagFixedColour tag
  | none => none

def wordGraphTagsAreFixed (graph : WordRegGraph) : Bool :=
  graph.tags.all (fun entry =>
    match entry.2 with
    | .fixed _ => true
    | .atemp | .stemp => false)

def wordGraphColouringRespectsEdges (graph : WordRegGraph) : Bool :=
  graph.adjacency.all (fun entry =>
    let node := entry.1
    entry.2.all (fun neighbour =>
      match wordGraphTagColour graph node,
        wordGraphTagColour graph neighbour with
      | some left, some right => left != right
      | _, _ => false))

structure WordRaState where
  graph : WordRegGraph
  active : List Nat
  degrees : NatInfoMap Nat
  simpWl : List Nat
  spillWl : List Nat
  stack : List Nat
  deriving Repr

def wordRaNodeIsAtemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .atemp => true
  | some (.fixed _) | some .stemp | none => false

def wordRaNodeIsStemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .stemp => true
  | some (.fixed _) | some .atemp | none => false

def wordRaDegree (graph : WordRegGraph) (node : Nat) : Nat :=
  (wordGraphNeighbours graph node).length

def wordRaDegrees (graph : WordRegGraph) : NatInfoMap Nat :=
  (List.range graph.dimension).map (fun node => (node, wordRaDegree graph node))

def wordRaRefreshWorklists (colours : Nat) (state : WordRaState) :
    WordRaState :=
  let simpWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree < colours
      | none => false)
  let spillWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree ≥ colours
      | none => false)
  { state with simpWl := simpWl, spillWl := spillWl }

def wordRaInit (colours : Nat) (graph : WordRegGraph) : WordRaState :=
  let active := List.range graph.dimension
  let state : WordRaState :=
    { graph := graph
      active := active
      degrees := wordRaDegrees graph
      simpWl := []
      spillWl := []
      stack := [] }
  wordRaRefreshWorklists colours state

def wordRaRemoveNode (colours : Nat) (node : Nat)
    (forceSpill : Bool) (state : WordRaState) : WordRaState :=
  let graph := if forceSpill then
      { state.graph with tags :=
          wordGraphUpdateTag node .stemp state.graph.tags }
    else
      state.graph
  let degrees := (wordGraphNeighbours state.graph node).foldl
    (fun degrees neighbour =>
      match lookupNatInfo neighbour degrees with
      | some degree =>
          (neighbour, degree - 1) :: degrees.filter
            (fun entry => entry.1 != neighbour)
      | none => degrees)
    state.degrees
  let state := { state with
    graph := graph
    active := state.active.erase node
    degrees := degrees
    simpWl := state.simpWl.erase node
    spillWl := state.spillWl.erase node
    stack := node :: state.stack }
  wordRaRefreshWorklists colours state

def wordRaSimplifyAll : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAll fuel colours
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | node :: _ =>
              wordRaSimplifyAll fuel colours
                (wordRaRemoveNode colours node true state)
          | [] => state

def wordRaFinalizeStemps (state : WordRaState) : WordRaState :=
  let stempNodes := state.active.filter (wordRaNodeIsStemp state.graph)
  { state with
    active := state.active.filter (fun node => !wordRaNodeIsStemp state.graph node)
    stack := stempNodes.reverse ++ state.stack }

def wordRaChooseColour (colours stackStart : Nat)
    (graph : WordRegGraph) (node : Nat) : Nat :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  match lookupNatInfo node graph.tags with
  | some .stemp => wordUnboundColour stackStart blocked
  | some .atemp =>
      match wordFirstAvailable
          (wordRemoveColours blocked (List.range colours)) blocked with
      | some colour => colour
      | none => wordUnboundColour stackStart blocked
  | some (.fixed colour) => colour
  | none => 0

def wordRaColourStack (colours stackStart : Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let colour := wordRaChooseColour colours stackStart graph node
      let graph := { graph with
        tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      wordRaColourStack colours stackStart nodes graph

def wordColourGraphWithWorklist (colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let state := wordRaInit colours graph
  let state := wordRaSimplifyAll (state.active.length + 1) colours state
  let state := wordRaFinalizeStemps state
  wordRaColourStack colours stackStart state.stack state.graph

/-! Move worklists and the first coalescing step.

    CakeML keeps move preferences separate from clash edges.  A move is first
    rejected when it is reflexive, already clashes, or has two fixed
    endpoints.  The remaining moves are canonicalised so a fixed endpoint is
    always the coalescing target.  The full CakeML allocator has additional
    freeze and move-revival phases; this section ports the data and the safe
    coalescing transition those phases build on.
-/

structure WordMove where
  priority : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def wordMoveEndpoints (move : WordMove) : List Nat :=
  [move.left, move.right]

def wordTagIsFixed : WordRegTag → Bool
  | .fixed _ => true
  | .atemp | .stemp => false

def wordTagIsAtemp : WordRegTag → Bool
  | .atemp => true
  | .fixed _ | .stemp => false

def wordGraphTagIs (predicate : WordRegTag → Bool)
    (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some tag => predicate tag
  | none => false

def wordMoveRelatedNodes (moves : List WordMove) : List Nat :=
  (moves.flatMap wordMoveEndpoints).eraseDups

def wordMoveConsistent (graph : WordRegGraph) (related : List Nat)
    (move : WordMove) : Bool :=
  let fixedLeft := wordGraphTagIs wordTagIsFixed graph move.left
  let fixedRight := wordGraphTagIs wordTagIsFixed graph move.right
  let leftMayMove := fixedLeft || (related.contains move.left)
  let rightMayMove := fixedRight || (related.contains move.right)
  move.left != move.right &&
    !(wordGraphNeighbours graph move.right).contains move.left &&
    leftMayMove && rightMayMove && !(fixedLeft && fixedRight)

def wordCanonicalizeMove (graph : WordRegGraph) (move : WordMove) : WordMove :=
  let leftFixed := wordGraphTagIs wordTagIsFixed graph move.left
  let rightFixed := wordGraphTagIs wordTagIsFixed graph move.right
  if rightFixed then
    { move with left := move.right, right := move.left }
  else if leftFixed then
    move
  else if move.left ≤ move.right then
    move
  else
    { move with left := move.right, right := move.left }

structure WordMoveWorklists where
  available : List WordMove
  unavailable : List WordMove
  deriving DecidableEq, Repr

def wordPrepareMoveWorklists (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveWorklists :=
  let related := wordMoveRelatedNodes moves
  moves.foldl (fun worklists move =>
    let move := wordCanonicalizeMove graph move
    if wordMoveConsistent graph related move then
      { worklists with available := worklists.available ++ [move] }
    else
      { worklists with unavailable := worklists.unavailable ++ [move] })
    { available := [], unavailable := [] }

def wordPreferenceMoves : List (Nat × Nat) → List WordMove
  | [] => []
  | (left, right) :: moves =>
      { priority := 0, left := left, right := right } ::
        wordPreferenceMoves moves

def wordParentUpdate (node parent : Nat)
    (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  (node, parent) :: parents.filter (fun entry => entry.1 != node)

def wordParentOf (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  match lookupNatInfo node parents with
  | some parent => parent
  | none => node

def wordCoalesceParentFuel : Nat → WordRegGraph → NatInfoMap Nat → Nat →
    Nat × NatInfoMap Nat
  | 0, _graph, parents, node => (wordParentOf parents node, parents)
  | fuel + 1, graph, parents, node =>
      let parent := wordParentOf parents node
      if parent = node then
        (node, parents)
      else if wordGraphTagIs wordTagIsFixed graph parent then
        (parent, parents)
      else if node ≤ parent then
        (node, parents)
      else
        let (ancestor, parents) :=
          wordCoalesceParentFuel fuel graph parents parent
        (ancestor, wordParentUpdate node ancestor parents)

structure WordMoveState where
  graph : WordRegGraph
  parents : NatInfoMap Nat
  related : List Nat
  available : List WordMove
  unavailable : List WordMove
  stack : List Nat
  deriving Repr

def wordInitMoveState (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveState :=
  let worklists := wordPrepareMoveWorklists graph moves
  { graph := graph
    parents := (List.range graph.dimension).map (fun node => (node, node))
    related := wordMoveRelatedNodes moves
    available := worklists.available
    unavailable := worklists.unavailable
    stack := [] }

def wordMoveReplaceNode (oldNode newNode : Nat) (move : WordMove) : WordMove :=
  { move with
    left := if move.left = oldNode then newNode else move.left
    right := if move.right = oldNode then newNode else move.right }

def wordResolveMove (state : WordMoveState) (move : WordMove) :
    WordMove × NatInfoMap Nat :=
  let (left, parents) := wordCoalesceParentFuel
    (state.graph.dimension + 1) state.graph state.parents move.left
  let (right, parents) := wordCoalesceParentFuel
    (state.graph.dimension + 1) state.graph parents move.right
  ({ move with left := left, right := right }, parents)

def wordCoalesceFreshNeighbours (graph : WordRegGraph)
    (target absorbed : Nat) : List Nat :=
  (wordGraphNeighbours graph absorbed).filter (fun node =>
    node != target && !(wordGraphNeighbours graph target).contains node)

def wordCoalesceSignificant (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some (.fixed _) => true
  | some .atemp | some .stemp => wordRaDegree graph node ≥ colours
  | none => true

def wordCoalesceSafe (colours : Nat) (graph : WordRegGraph)
    (related : List Nat) (move : WordMove) : Bool :=
  if !wordMoveConsistent graph related move then
    false
  else
    let move := wordCanonicalizeMove graph move
    let target := move.left
    let absorbed := move.right
    let fresh := wordCoalesceFreshNeighbours graph target absorbed
    if wordGraphTagIs wordTagIsFixed graph target then
      fresh.all (fun node => !wordCoalesceSignificant colours graph node)
    else
      let neighbours :=
        (wordGraphNeighbours graph target ++
          wordGraphNeighbours graph absorbed).eraseDups
      (neighbours.filter (wordCoalesceSignificant colours graph)).length < colours

def wordCoalesceMove (colours : Nat) (state : WordMoveState)
    (move : WordMove) : Option WordMoveState :=
  let (move, parents) := wordResolveMove state move
  let state := { state with parents := parents }
  let move := wordCanonicalizeMove state.graph move
  if !wordCoalesceSafe colours state.graph state.related move then
    none
  else
    let fresh := wordCoalesceFreshNeighbours
      state.graph move.left move.right
    let graph := fresh.foldl
      (fun graph node => wordGraphInsertEdge move.left node graph)
      state.graph
    let parents := wordParentUpdate move.right move.left state.parents
    let pending := (state.available ++ state.unavailable).map
      (wordMoveReplaceNode move.right move.left)
    let worklists := wordPrepareMoveWorklists graph pending
    some
      { graph := graph
        parents := parents
        related := wordMoveRelatedNodes pending
        available := worklists.available
        unavailable := worklists.unavailable
        stack := move.right :: state.stack }

/-! Repeated coalescing mirrors CakeML's  loop.  Invalid moves
    are retired to the unavailable list, while a successful merge rebuilds
    the pending worklists so moves that became useful are reconsidered. -/

def wordCoalesceAll : Nat → Nat → WordMoveState → WordMoveState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.available with
      | [] => state
      | move :: moves =>
          if wordCoalesceSafe colours state.graph state.related move then
            match wordCoalesceMove colours state move with
            | some state => wordCoalesceAll fuel colours state
            | none =>
                wordCoalesceAll fuel colours
                  { state with
                    available := moves
                    unavailable := move :: state.unavailable }
          else
            wordCoalesceAll fuel colours
              { state with
                available := moves
                unavailable := move :: state.unavailable }

def wordCoalesceAllAvailable (colours : Nat) (state : WordMoveState) :
    WordMoveState :=
  wordCoalesceAll
    (state.available.length + state.unavailable.length + state.graph.dimension + 1)
    colours state

structure WordRegAllocInput where
  bijection : WordBijection
  graph : WordRegGraph
  deriving Repr

def wordInitRegAlloc (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat) :
    WordRegAllocInput :=
  let bijection := wordMkBijection tree
  let emptyGraph : WordRegGraph :=
    { adjacency := [], tags := [], dimension := bijection.next }
  let graphResult := wordMkGraph
    (wordBijectionToNode bijection) tree [] emptyGraph
  let graph := forced.foldl
    (fun graph edge =>
      wordGraphInsertEdge
        (wordBijectionToNode bijection edge.1)
        (wordBijectionToNode bijection edge.2) graph)
    graphResult.graph
  { bijection := bijection
    graph := { graph with
      tags := wordMkTags bijection.next fixedSources bijection.fromNode } }

/-! Bridge the graph allocator back to source variables.

    CakeML stores compressed graph colours and applies  only at
    the Word boundary.  In particular, physical source variables are tagged
    with half their architectural register number and total colours are
    doubled again.  Keeping this conversion explicit avoids accidentally
    treating a graph colour as a RISC-V register number. -/

def wordGraphNodeFinalColour (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  let (root, _) := wordCoalesceParentFuel
    (graph.dimension + 1) graph parents node
  match wordGraphTagColour graph root with
  | some colour => colour
  | none => 0

def wordGraphTotalColourAt (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  2 * wordGraphNodeFinalColour graph parents node

def wordGraphColouringAt (colouring : NatInfoMap Nat)
    (source : Nat) : Nat :=
  match lookupNatInfo source colouring with
  | some colour => colour
  | none => if source % 2 == 0 then source else 0

def wordGraphTotalColouring (input : WordRegAllocInput)
    (graph : WordRegGraph) (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  input.bijection.fromNode.map (fun entry =>
    (entry.2, wordGraphTotalColourAt graph parents entry.1))

structure WordGraphAllocation where
  graph : WordRegGraph
  colouring : NatInfoMap Nat
  parents : NatInfoMap Nat
  deriving Repr

def wordAllocateGraph (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moveState := wordInitMoveState input.graph (wordPreferenceMoves moves)
  let moveState := wordCoalesceAllAvailable colours moveState
  let graph := wordColourGraphWithWorklist colours stackStart moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

theorem wordAllocateGraph_sound (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraph tree forced fixedSources moves colours stackStart =
      some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraph] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordProgForcedClashes : WordProg α → List (Nat × Nat)
  | .skip | .store _ _ | .set _ _ | .break _ | .continue _ |
      .raise _ | .return _ _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ => []
  | .assign _ _ => []
  | .inst instruction => wordInstForcedClashes instruction
  | .seq first second =>
      wordProgForcedClashes first ++ wordProgForcedClashes second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgForcedClashes thenBranch ++ wordProgForcedClashes elseBranch
  | .loop _ body _ => wordProgForcedClashes body
  | .call _ _ _ none => []
  | .call _ _ _ (some (_, body)) => wordProgForcedClashes body
  | .shareInst _ _ _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateGraphProgram (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordGraphAllocation × WordProg α) :=
  let tree := wordClashTree program []
  let forced := wordProgForcedClashes program
  let moves := wordProgPreferenceEdges program
  (wordAllocateGraph tree forced fixedSources moves colours stackStart).map
    (fun allocation =>
      (allocation,
        wordApplyColour
          (wordGraphColouringAt allocation.colouring) program))

end Flapjack
