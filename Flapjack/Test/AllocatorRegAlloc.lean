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

example :
    wordGraphTagColour
        (wordColourGraph 2 2 2
          (wordInitRegAlloc (.delta [0, 1] []) [] []).graph) 1 =
      some 1 := by
  native_decide

example :
    wordGraphColouringRespectsEdges
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  native_decide

example :
    wordGraphTagColour
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) 1 =
      some 1 := by
  native_decide

example :
    wordGraphTagsAreFixed
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  native_decide

example :
    wordGraphColouringRespectsEdges
        (wordColourGraphWithWorklist 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  native_decide

example :
    wordGraphTagsAreFixed
      (wordColourGraphWithWorklist 1 1
        (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  native_decide

def moveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .atemp), (1, .atemp)]
    dimension := 2 }

def fixedMoveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .fixed 3), (1, .atemp)]
    dimension := 2 }

def fixedRightMoveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .atemp), (1, .fixed 3)]
    dimension := 2 }

def move01 : WordMove :=
  { priority := 7, left := 0, right := 1 }

example :
    wordPrepareMoveWorklists moveWorklistGraph [move01] =
      { available := [move01], unavailable := [] } := by
  native_decide

example :
    wordPrepareMoveWorklistsWithColours 1 fixedMoveWorklistGraph [move01] =
      { available := [], unavailable := [move01] } := by
  native_decide

example :
    wordPrepareMoveWorklistsWithColours 4 fixedMoveWorklistGraph [move01] =
      { available := [move01], unavailable := [] } := by
  native_decide

def briggsMoveGraph : WordRegGraph :=
  { adjacency := [(1, [2]), (2, [1, 3]), (3, [2])]
    tags := [(0, .atemp), (1, .atemp), (2, .atemp), (3, .atemp)]
    dimension := 4 }

example : wordBgOk 2 briggsMoveGraph 0 1 = some ([], [2]) := by
  native_decide

example : wordBgOk 1 briggsMoveGraph 0 1 = none := by
  native_decide

example : wordCoalesceSafe 1 briggsMoveGraph [0, 1] move01 = false := by
  native_decide

example :
    wordPrepareMoveWorklists moveWorklistGraph
      [{ priority := 0, left := 0, right := 0 }] =
      { available := [],
        unavailable := [{ priority := 0, left := 0, right := 0 }] } := by
  native_decide

example :
    wordPrepareMoveWorklists
      { adjacency := [(0, [1]), (1, [0])]
        tags := [(0, .atemp), (1, .atemp)]
        dimension := 2 }
      [move01] =
      { available := [], unavailable := [move01] } := by
  native_decide

example :
    wordCanonicalizeMove fixedMoveWorklistGraph move01 =
      { priority := 7, left := 0, right := 1 } := by
  native_decide

example :
    wordCanonicalizeMove fixedRightMoveWorklistGraph move01 =
      { priority := 7, left := 1, right := 0 } := by
  native_decide

example :
    (wordCoalesceParentFuel 4 moveWorklistGraph
      [(0, 0), (1, 0), (2, 1)] 2) =
      (0, [(2, 0), (1, 0), (0, 0)]) := by
  native_decide

example :
    (wordCoalesceMove 1
      (wordInitMoveState fixedMoveWorklistGraph [move01]) move01).map
        (fun state => lookupNatInfo 1 state.parents) = some (some 0) := by
  native_decide

example :
    (wordCoalesceMove 1
      (wordInitMoveState fixedMoveWorklistGraph [move01]) move01).map
        (fun state => state.stack) = some [1] := by
  native_decide

example :
    let state := wordInitMoveState
      { adjacency := []
        tags := [(0, .fixed 3), (1, .atemp), (2, .atemp)]
        dimension := 3 }
      [move01, { priority := 2, left := 1, right := 2 }]
    let state := wordCoalesceAllAvailable 1 state
    lookupNatInfo 2 state.parents = some 0 ∧ state.stack = [2, 1] ∧
      state.available = [] := by
  native_decide

example : wordGraphColouringAt [(4, 8)] 4 = 8 := by
  native_decide

example : wordGraphColouringAt [(4, 8)] 6 = 6 := by
  native_decide

example :
    (wordAllocateGraph (.delta [0, 1] []) [] [] [] 1 1).isSome = true := by
  native_decide

example :
    (wordAllocateGraph (.delta [0, 1] []) [] [] [] 1 1).map
        (fun allocation =>
          (lookupNatInfo 0 allocation.colouring,
            lookupNatInfo 1 allocation.colouring)) =
      some (some 0, some 2) := by
  native_decide

example :
    wordProgForcedClashes
      (.inst (.arith (.longMul 4 5 6 7)) : WordProg Nat) =
      [(4, 5), (4, 6), (4, 7)] := by
  native_decide

example :
    (wordAllocateGraphProgram
      (.assign 2 (.var 3) : WordProg Nat) [] 1 1).map
        (fun allocation =>
          match allocation.2 with
          | .assign destination (.var source) => (destination, source)
          | _ => (0, 0)) =
      some (2, 2) := by
  native_decide

end Flapjack
