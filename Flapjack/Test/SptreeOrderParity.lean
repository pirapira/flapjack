import Flapjack.NumSet
import Flapjack.RiscV.Allocator

/-! Direct HOL parity for CakeML's `sptree$toAList` enumeration order, which
    the word allocator uses at its three SSA boundaries (`fix_inconsistencies`,
    `ssa_reconcile`, `loop_setup`).  The expected values come from evaluating
    `MAP FST (toAList (fromAList ...))` in HOL:
    `[0,4,6,12] -> [0,4,12,6]`, `[0,4,8,12,16] -> [0,16,8,4,12]`,
    `[1,2,3,4,5] -> [3,1,5,4,2]`, `List.range 13 ->
    [7,3,11,1,9,5,0,8,4,12,2,10,6]`. -/

namespace Flapjack.Test.SptreeOrderParity

open Flapjack

def sptreeOrderGuard : Bool :=
  NumSet.fromList [0, 4, 6, 12] == [0, 4, 12, 6] &&
    NumSet.fromList [0, 4, 8, 12, 16] == [0, 16, 8, 4, 12] &&
    NumSet.fromList [1, 2, 3, 4, 5] == [3, 1, 5, 4, 2] &&
    NumSet.fromList (List.range 13) ==
      [7, 3, 11, 1, 9, 5, 0, 8, 4, 12, 2, 10, 6]

#guard sptreeOrderGuard

/-- The enumeration is genuinely not ascending, and `ssa_reconcile` emits its
    parallel move in that order: with every target name defaulting to `0`, the
    four loop variables `{0,4,6,12}` must appear as `0,4,12,6`. -/
def wordSsaReconcileOrderGuard : Bool :=
  match wordSsaReconcileTo (α := Nat)
      ({ current := [(0, 21), (4, 41), (6, 33), (12, 37)], next := 200 } :
        WordSsaState)
      ({ current := [], next := 200 } : WordSsaState)
      [0, 4, 6, 12] with
  | .move 1 moves => moves == [(0, 21), (0, 41), (0, 37), (0, 33)]
  | _ => false

#guard wordSsaReconcileOrderGuard

/-- `fix_inconsistencies` consumes the same Cake tree order.  Its recursive
    fake-move pass emits the corresponding sequence in reverse recursion order;
    pin that observable order as well as the merged SSA names. -/
def wordSsaFixInconsistenciesOrderGuard : Bool :=
  match wordSsaFixInconsistencies (α := Nat) none
      ({ current := [(0, 21), (4, 41), (6, 33), (12, 37)], next := 200 } :
        WordSsaState)
      ({ current := [], next := 200 } : WordSsaState) 200 with
  | (state, leftMoves, rightMoves) =>
      state.current == [(0, 212), (4, 208), (12, 204), (6, 200)] &&
        state.next == 216 &&
        wordProgReadVars leftMoves == [33, 37, 41, 21] &&
        wordProgWriteVars leftMoves == [200, 204, 208, 212] &&
        wordProgReadVars rightMoves == [] &&
        wordProgWriteVars rightMoves == [200, 204, 208, 212]

#guard wordSsaFixInconsistenciesOrderGuard

/-- `loop_setup` refreshes names in the Patricia-tree order rather than the
    source list order.  This set makes the non-ascending `[0,4,12,6]` order
    visible in the generated refresh move and resulting SSA map. -/
def wordSsaLoopSetupOrderGuard : Bool :=
  match wordSsaLoopSetup (α := Nat)
      ({ current := [(0, 21), (4, 41), (6, 33), (12, 37)], next := 200 } :
        WordSsaState) [0, 4] [6, 12] with
  | (state, .move 0 moves) =>
      state.current == [(6, 212), (12, 208), (4, 204), (0, 200)] &&
        state.next == 216 &&
        moves == [(200, 21), (204, 41), (208, 37), (212, 33)]
  | _ => false

#guard wordSsaLoopSetupOrderGuard

def parityGuard : Bool :=
  sptreeOrderGuard && wordSsaReconcileOrderGuard &&
    wordSsaFixInconsistenciesOrderGuard && wordSsaLoopSetupOrderGuard

#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake toAList order parity"
  else
    IO.println "FAIL Cake toAList order parity"
  pure parityGuard

end Flapjack.Test.SptreeOrderParity
