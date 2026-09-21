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

example
    (context : PanValueFfiContext Nat)
    (initial : PanValueFfiProgramState Nat Unit)
    (clock : Nat) (primitive : PanPrimitiveHandler Nat)
    (handler : PanValueStatefulFfiHandler Nat Unit)
    (fuel : Nat) (declarations : List (Decl Nat))
    (entry : FunName) (arguments : List (Exp Nat))
    (state : PanValueProgramState Nat)
    (outcome : PanValueFfiClockOutcome Nat Unit) (nextClock : Nat)
    (hdeclarations : evalPanValueDeclarations initial.source declarations = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes)) = some (outcome, nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments = some (outcome, nextClock) :=
  evalPanValueFfiClockProgram_of_declarations_and_call context initial clock primitive
    handler fuel declarations entry arguments state outcome nextClock
    (hdeclarations := hdeclarations) (hentry := hentry) (hcall := hcall)

end Flapjack
