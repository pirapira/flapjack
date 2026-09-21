import Flapjack.PanValueFfiClockCorrectness
import Flapjack.Test.PanValueFfiSemantics

namespace Flapjack
open RiscV

/-- A successful one-step leaf run at clock five returns exactly clock five. -/
example : (5 : Nat) ≤ 5 := by
  have hrun : evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive statefulTestHandler
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 1
      (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState 5
      (.skip : Prog (Word 64)) = some (.control (.normal (fun _ => none) (fun _ => none)
        statefulTestMemory statefulTestFinalState), 5) := by
    simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  exact evalPanValueFfiClockProg_clock_le statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 1
    (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState 5
    (.skip : Prog (Word 64)) none none none
    (.control (.normal (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState)) 5 hrun

end Flapjack
