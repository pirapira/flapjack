import Flapjack.RiscV.SpillCosts

/-!
Parity regressions for the hashed heuristic state.

`wordHeuristicSpillCostsFast` replaces the association-list counter map of
`wordHeuristic` with a `Std.TreeMap` plus an update stamp.  The reference
definition makes the *order* of its result observable -- every counter bump
moves its key to the front of the list -- so these checks compare the two
implementations as lists, not as sets, across every constructor that touches
the counter state, including both merge paths (`ite` and a handled call).
-/

namespace Flapjack

/-- Covers `move`, `inst`, `get`, `set`, `opCurrHeap`, `locValue` and `seq`. -/
def heuristicParityStraightLine : WordProg Nat :=
  .seq (.move 5 [(9, 10), (11, 9)])
    (.seq (.inst (.arith (.longMul 0 1 2 3)))
      (.seq (.inst (.mem .store32 9 12))
        (.seq (.inst (.const 4 7))
          (.seq (.get 6 .currHeap)
            (.seq (.set .currHeap (.var 6))
              (.seq (.opCurrHeap .add 8 9)
                (.locValue 13 2)))))))

/-- Covers the `ite` merge, i.e. `wordHeuristicMaxAll` over two maps with
    overlapping and disjoint keys, plus the condition counters that are
    applied to the merged map afterwards. -/
def heuristicParityMerge : WordProg Nat :=
  .seq (.inst (.const 1 5))
    (.ite .equal 4 (.reg 5)
      (.seq (.get 4 .currHeap) (.inst (.arith (.binOp .add 20 21 (.reg 22)))))
      (.seq (.inst (.mem .load 4 30))
        (.inst (.arith (.shift .lsl 20 23 (.imm 2))))))

/-- Covers the handled-call merge and the self-call path that folds the whole
    key list into the call set (`wordHeuristicAddCall`). -/
def heuristicParityCall : WordProg Nat :=
  .seq (.inst (.const 40 1))
    (.call (some ([1], ([], []), .seq (.move 3 [(10, 11)]) (.get 12 .currHeap), 0, 0))
      (some 7) []
      (some (2, .seq (.move 5 [(20, 21)]) (.inst (.mem .store 10 40)), 0, 0)))

/-- Nested self-calls: the continuation of each call is the rest of the
    function, which is the shape that made the reference definition cubic. -/
def heuristicParityNestedCalls : Nat → WordProg Nat
  | 0 => .inst (.const 99 0)
  | depth + 1 =>
      .call (some ([depth], ([], []), heuristicParityNestedCalls depth, 0, 0))
        (some 7) [] none

def heuristicParityLoop : WordProg Nat :=
  .loop [1, 2] (.seq (.inst (.arith (.div 1 2 3))) (.shareInst .load8 9 (.var 1))) [1]

/-- Whole-state parity, list order included, for every fixture above. -/
def heuristicParityStates (currentFunction : Nat) (program : WordProg Nat) : Bool :=
  let reference := wordHeuristic currentFunction program ([], [])
  let fast := wordHeuristicFast currentFunction program ({}, {})
  fast.1.toNatInfoMap == reference.1 && fast.2.names == reference.2

def heuristicParitySpillCosts (currentFunction : Nat) (program : WordProg Nat) : Bool :=
  wordHeuristicSpillCostsFast currentFunction program ==
    wordHeuristicSpillCosts currentFunction program

/- Cake's move case updates all RHS registers before all LHS registers.  The
   order is observable because each update moves its key to the front. -/
def heuristicMoveUpdateOrderGuard : Bool :=
  (wordHeuristic 7 (.move 1 [(1, 2), (3, 4)] : WordProg Nat) ([], [])).1.map
      Prod.fst == [1, 3, 2, 4]

#guard heuristicMoveUpdateOrderGuard

def heuristicParityPrograms : List (Nat × WordProg Nat) :=
  [(7, heuristicParityStraightLine), (7, heuristicParityMerge),
   (7, heuristicParityCall), (3, heuristicParityCall),
   (7, heuristicParityNestedCalls 12), (7, heuristicParityLoop),
   (7, .seq heuristicParityMerge heuristicParityCall),
   (7, .mustTerminate (.seq heuristicParityStraightLine heuristicParityMerge)),
   (7, .ite .less 20 (.imm 3) heuristicParityCall heuristicParityMerge)]

#guard heuristicParityPrograms.all
  (fun entry => heuristicParityStates entry.1 entry.2)

#guard heuristicParityPrograms.all
  (fun entry => heuristicParitySpillCosts entry.1 entry.2)

/-! `natEraseDups` must agree with `List.eraseDups`, which is what fixes the
    key order of the merge and, in `Flapjack/RiscV/WordDeadCode.lean`, the
    live-set order. -/
def heuristicEraseDupsCases : List (List Nat) :=
  [[], [7], [7, 7], [3, 1, 3, 4, 1, 5, 4], [1, 2, 3, 4, 5],
   [5, 4, 3, 2, 1], [9, 9, 9, 9], [0, 1, 0, 2, 0, 3, 1, 2, 3],
   List.range 40 ++ List.range 40, (List.range 40).reverse ++ List.range 20]

#guard heuristicEraseDupsCases.all
  (fun names => names.eraseDups == natEraseDups names)

/-! The merged map's order is the deduplicated key list reversed; pin it
    directly so a change in either implementation is visible here. -/
#guard (wordHeuristicFast 7 heuristicParityMerge ({}, {})).1.keys ==
  (wordHeuristic 7 heuristicParityMerge ([], [])).1.map Prod.fst

end Flapjack
