import Flapjack.RiscV.CorrectnessGraphCoverage

namespace Flapjack

open RiscV

/-! The graph coverage theorem is usable at the exact allocator result
    boundary, without exposing the allocator's internal worklists. -/

example (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (moves : List (Nat × Nat))
    (colours stackStart : Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraph tree forced fixedSources moves colours stackStart =
      some allocation) :
    ∀ name, name ∈ wordClashTreeNames tree →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  exact wordAllocateGraph_maps_clash_names tree forced fixedSources moves
    colours stackStart allocation halloc

def graphCoverageRegressionTree : WordClashTree :=
  .seq (.set [1, 2]) (.branch (some [3]) (.delta [4] [1]) (.delta [] [3]))

def graphCoverageRegressionAllocation : Option WordGraphAllocation :=
  wordAllocateGraph graphCoverageRegressionTree [] [] [] 13 14

#guard graphCoverageRegressionAllocation.isSome

end Flapjack
