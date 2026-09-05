import Flapjack.Test.StructuredCalls

namespace Flapjack

def flatTestFfi : PanFlatFfiHandler Nat :=
  fun function configuration _ array _ locals =>
    if function == "host" then
      some (updatePanValueMap locals "out" (.word (configuration + array)))
    else none

example :
    (evalPanFlatProgWithCallsAndFfi (α := Nat) [] [] flatTestFfi
      0 100 1 20 (fun _ => none) (fun _ => none) (fun _ => true) (fun _ => none)
      (.extCall "host" (.const 2) (.const 1) (.const 5) (.const 1))).map
      (fun result => match result with
        | .normal locals _ _ => locals "out"
        | _ => none) = some (some (.word 7)) := by
  simp [evalPanFlatProgWithCallsAndFfi,
    evalPanFlatProgWithPrimitiveAndFfi, evalPanFlatProgFuelWithPrimitiveAndFfi,
    evalPanFlatExp, evalPanFlatExps, evalPanFlatExp.evalPanFlatExps,
    flatTestFfi, updatePanValueMap]

example :
    (evalPanFlatProgWithCallsAndFfi (α := Nat) [] [] flatNoFfi
      0 100 1 8 (fun _ => none) (fun _ => none) (fun _ => true) (fun _ => none)
      (.while (.const 0) .break)).map
      (fun result => match result with
        | .normal _ _ _ => true
        | _ => false) = some true := by
  simp [evalPanFlatProgWithCallsAndFfi,
    evalPanFlatProgWithPrimitiveAndFfi, evalPanFlatProgFuelWithPrimitiveAndFfi,
    evalPanFlatExp, flatNoFfi]

def structuredTestFfi : PanValueFfiHandler Nat :=
  fun function configuration _ array _ locals =>
    if function == "host" then
      some (updatePanValueMap locals "out" (.word (configuration + array)))
    else none

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) [] [] structuredTestFfi
      0 100 8 20 (fun _ => none) (fun _ => none) (fun _ => none)
      (.extCall "host" (.const 2) (.const 1) (.const 5) (.const 1))).map
      (fun result => match result with
        | .normal locals _ _ => locals "out"
        | _ => none) = some (some (.word 7)) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueExtCall,
    evalPanValueExp, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    structuredTestFfi, updatePanValueMap]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) [] [] structuredNoFfi
      0 100 8 8 (fun _ => none) (fun _ => none) (fun _ => none)
      (.seq (.store (.const 4) (.const 9))
        (.return (.load .one (.const 4))))).map
      (fun result => match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some 9) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueExp, isWfShape,
    isWfShape.isWfShapeList, evalPanValueExps,
    evalPanValueExp.evalPanValueExps, structuredNoFfi, updatePanValueMap,
    updatePanValueMemory, panValueShape, panShapeMatches]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) [] [] structuredNoFfi
      0 100 8 5 (fun _ => none) (fun _ => none) (fun _ => none)
      (.while (.const 0) (.break))).map
      (fun result => match result with
        | .normal _ _ _ => true
        | _ => false) = some true := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueExp, structuredNoFfi]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) [] [] structuredNoFfi
      0 100 8 8 (fun _ => none) (fun _ => none) (fun _ => none)
      (.dec "scoped" .one (.const 9)
        (.return (.var .local "scoped")))).map
      (fun result => match result with
        | .returned locals _ _ [PanValue.word value] =>
            (locals "scoped", value)
        | _ => (none, 0)) = some (none, 9) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueExp,
    structuredNoFfi, updatePanValueMap, restorePanValueLocal,
    restorePanValueControlLocal, panValueShape, panShapeMatches]

end Flapjack
