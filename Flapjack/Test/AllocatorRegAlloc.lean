import Flapjack.RiscV.RegAlloc

namespace Flapjack

/-! Regression tests for the CakeML graph allocator data model. -/

example : wordTagForSource [] 1 = .atemp := by
  rfl

example : wordTagForSource [1] 1 = .stemp := by
  rfl

example : wordTagForSource [] 3 = .stemp := by
  rfl

example : wordTagForSource [] 4 = .fixed 2 := by
  rfl

example :
    (wordMkBijection
      (.seq (.delta [4] [2]) (.delta [5] [3]))).next = 4 := by
  native_decide

example :
    lookupNatInfo 4
        (wordMkBijection
          (.seq (.delta [4] [2]) (.delta [5] [3]))).toNode = some 2 := by
  native_decide

example :
    lookupNatInfo 0
        (wordInitRegAlloc (.delta [0, 1] [2]) [] []).graph.adjacency =
      some [1] := by
  native_decide

example :
    lookupNatInfo 1
        (wordInitRegAlloc (.delta [0, 1] [2]) [] []).graph.adjacency =
      some [0] := by
  native_decide

end Flapjack
