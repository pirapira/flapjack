import Flapjack.CrepToLoopCorrectness

/-! Concrete regression for the Crepe-to-Loop FFI state correspondence. -/

namespace Flapjack

def crepLoopFfiState : CrepState Nat :=
  { locals := fun name =>
      if name == 1 then some 41
      else if name == 2 then some 0
      else if name == 3 then some 0
      else if name == 4 then some 0
      else none
    memory := fun _ => none }

def crepLoopFfi : CrepFfiHandler Nat :=
  fun _ configuration _ _ _ state =>
    some { state with locals := updateCrepLocal state.locals 9 (configuration + 1) }

def crepLoopFfiStateAfter : CrepState Nat :=
  { crepLoopFfiState with
    locals := updateCrepLocal crepLoopFfiState.locals 9 42 }

theorem crepToLoop_extCall_simulation_regression :
    evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 4 crepLoopFfiState
        (.extCall "inc" 1 2 3 4) =
        some (.normal crepLoopFfiStateAfter) ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFfi) 4
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
          [9] (.extCall "inc" 1 2 3 4)) =
        some (.normal (loopStateOfCrepState crepLoopFfiStateAfter)) := by
  apply crepToLoop_extCall_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState crepLoopFfiStateAfter [9] "inc" 1 2 3 4
    41 0 0 0
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfi, crepLoopFfiState, crepLoopFfiStateAfter]

theorem crepToLoop_return_raise_regression :
    (evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 1 crepLoopFfiState
        (.return [.const 42])).map crepControlValues =
        (evalLoopProgWithCallsAndFfi []
          (fun _ _ _ _ _ loopState => some loopState) 12
          (loopStateOfCrepState crepLoopFfiState)
          (loopCompileProg
            ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
              LoopContext Nat)
            [9] (.return [.const 42]))).map loopResultValues ∧
    (evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 1 crepLoopFfiState
        (.raise 17)).map crepControlException =
        (evalLoopProgWithCallsAndFfi []
          (fun _ _ _ _ _ loopState => some loopState) 8
          (loopStateOfCrepState crepLoopFfiState)
          (loopCompileProg
            ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
              LoopContext Nat)
            [9] (.raise 17))).map loopControlException := by
  constructor
  · exact crepToLoop_return_const_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
      [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
      0 100 0 crepLoopFfiState [9] 42
  · exact crepToLoop_raise_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
      [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
      0 100 0 crepLoopFfiState [9] 17

end Flapjack
