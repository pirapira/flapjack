import Flapjack.RiscV.CorrectnessGraphLocations

/-! Regression coverage for graph-allocation source locations. -/

namespace Flapjack

def graphLocationTestAllocation : WordGraphAllocation :=
  { bijection :=
      { toNode := [(7, 0)], fromNode := [(0, 7)], next := 1 }
    initialTags := []
    graph := { adjacency := [], tags := [], dimension := 1 }
    colouring := []
    parents := [] }

example :
    lookupNatInfo 7 (wordGraphLocations graphLocationTestAllocation 2 0) =
      some (.stack 0) := by
  rfl

example :
    ∃ location,
      lookupNatInfo 7 (wordGraphLocations graphLocationTestAllocation 2 0) =
        some location := by
  apply wordGraphLocations_lookup_of_fromNode
    graphLocationTestAllocation 2 0 7 0
  rfl

end Flapjack
