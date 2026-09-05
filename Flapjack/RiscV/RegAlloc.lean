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

end Flapjack
