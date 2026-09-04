import Flapjack.Test.Loops

namespace Flapjack

open RiscV

def structuredValueTestContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def flatPairDomain : PanMemoryDomain Nat :=
  fun address => address == 10 || address == 11

def flatPairMemory : PanFlatMemory Nat :=
  fun address => if address == 10 then some 3
    else if address == 11 then some 5 else none

example : panValueWords (.rStruct [.word (3 : Nat), .word 5]) = [3, 5] := by
  rfl

example :
    panFlatLoad structuredValueTestContext flatPairDomain flatPairMemory 1 10
      (.comb [.one, .one]) =
      some (.rStruct [.word 3, .word 5]) := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, flatPairDomain, flatPairMemory,
    panFlatReadWord, panOffset, panStructContextFuel, panShapeFieldsFuel,
    panShapeFuel, panShapeFuel.panShapeListFuel, shapeSizeWithContext,
    isWfShape, isWfShape.isWfShapeList, lookupInfo, structuredValueTestContext]

example :
    panFlatLoad structuredValueTestContext flatPairDomain flatPairMemory 1 10
      (.named "Pair") =
      some (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, flatPairDomain, flatPairMemory,
    panFlatReadWord, panOffset, panStructContextFuel, panShapeFieldsFuel,
    panShapeFuel, panShapeFuel.panShapeListFuel, shapeSizeWithContext,
    isWfShape, isWfShape.isWfShapeList, lookupInfo, structuredValueTestContext]

example :
    panFlatLoad structuredValueTestContext
      (fun address => address == 10) flatPairMemory 1 10
      (.comb [.one, .one]) = none := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, flatPairMemory, panFlatReadWord,
    panOffset, panStructContextFuel, panShapeFieldsFuel, panShapeFuel,
    panShapeFuel.panShapeListFuel, shapeSizeWithContext, isWfShape,
    isWfShape.isWfShapeList, lookupInfo]

example :
    (panFlatStore flatPairDomain (fun _ => none) 1 10
      (.rStruct [.word (3 : Nat), .word 5])).bind
      (fun memory => panFlatLoad structuredValueTestContext flatPairDomain memory
        1 10 (.comb [.one, .one])) =
      some (.rStruct [.word 3, .word 5]) := by
  simp [panFlatStore, panFlatStoreWords, panFlatStoreWord, panValueWords,
    panValueFuel, panValueFuel.panValueListFuel, panValueWordsFuel,
    panValueWordsFuel.panValueWordsListFuel,
    panOffset, panFlatLoad, panFlatLoadFuel,
    panFlatLoadFuel.panFlatLoadListFuel, panFlatLoadFuel.panFlatLoadFieldsFuel,
    flatPairDomain, panFlatReadWord, panStructContextFuel, panShapeFieldsFuel,
    panShapeFuel, panShapeFuel.panShapeListFuel, shapeSizeWithContext,
    isWfShape, isWfShape.isWfShapeList, lookupInfo, updatePanValueMap]

example :
    (evalPanFlatProg (α := Nat) structuredValueTestContext 0 100 1
      (fun _ => none) (fun _ => none) flatPairDomain (fun _ => none)
      (.seq (.store (.const 10)
        (.rStruct [.const 3, .const 5]))
        (.return (.load (.comb [.one, .one]) (.const 10))))).map
      (fun result => result.2.2.2) =
      some [PanValue.rStruct [.word 3, .word 5]] := by
  simp [evalPanFlatProg, evalPanFlatProgWithPrimitive, evalPanFlatExp,
    evalPanFlatExp.evalPanFlatExps, evalPanFlatExps, panFlatStore,
    panFlatStoreWords, panFlatStoreWord, panValueWords, panValueWordsFuel,
    panValueFuel, panValueFuel.panValueListFuel, panValueWordsFuel,
    panValueWordsFuel.panValueWordsListFuel, panOffset, panFlatLoad,
    panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, flatPairDomain, panFlatReadWord,
    panStructContextFuel, panShapeFieldsFuel, panShapeFuel,
    panShapeFuel.panShapeListFuel, shapeSizeWithContext, isWfShape,
    isWfShape.isWfShapeList, lookupInfo, updatePanValueMap]

example :
    evalPanValueExp (α := Nat) structuredValueTestContext
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.nField "right"
        (.nStruct "Pair" [("left", .const 3), ("right", .const 5)])) =
      some (.word 5) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
    evalPanValueExp.evalPanValueFields, structuredValueTestContext,
    panValueFieldsHaveShapes, panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches, lookupInfo, lookupPanValueField]

example :
    evalPanValueExp (α := Nat) structuredValueTestContext
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.nStruct "Pair" [("left", .const 3),
        ("right", .rStruct [.const 4, .const 5])]) = none := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueFields,
    evalPanValueExp.evalPanValueExps, structuredValueTestContext,
    panValueFieldsHaveShapes, panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches, lookupInfo]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun name => if name == "g" then some (.word 11) else none)
      (fun _ => none) 0 100 8 (.var .global "g") = some (.word 11) := by
  simp [evalPanValueExp]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none)
      (fun address => if address == 4 then
        some (.rStruct [.word 1, .word 2]) else none)
      0 100 8 (.load (.comb [.one, .one]) (.const 4)) =
      some (.rStruct [.word 1, .word 2]) := by
  simp [evalPanValueExp, isWfShape, isWfShape.isWfShapeList,
    panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none)
      (fun address => if address == 4 then some (.word 2) else none)
      0 100 8 (.load (.named "Unknown") (.const 4)) = none := by
  simp [evalPanValueExp, isWfShape, panValueShape, panShapeMatches]

example :
    (evalPanValueProg (α := Nat) [] 0 100 8
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.seq (.assign .local "x" (.const 9))
        (.return (.var .local "x")))).map
      (fun result => result.2.2.2) = some [PanValue.word 9] := by
  simp [evalPanValueProg, evalPanValueProgWithPrimitive,
    evalPanValueExp, updatePanValueMap]

def structuredCallTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

def structuredNoFfi : PanValueFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) []
      structuredCallTestFunctions structuredNoFfi 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.call (some (some (.local, "result"), none)) "id" [.const 7])).map
      (fun result => match result with
        | .normal locals _ _ => locals "result"
        | _ => none) = some (some (.word 7)) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueCallWithCallsAndFfi,
    evalPanValueExp, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    structuredCallTestFunctions, structuredNoFfi, bindPanValueParameters,
    assignPanValueCallResult, updatePanValueMap, lookupPanFunction]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) []
      [("fail", [], .raise "E" (.const 9))] structuredNoFfi 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.call (some (none, some ("E", "caught",
        .return (.var .local "caught")))) "fail" [])).map
      (fun result => match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some 9) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueCallWithCallsAndFfi,
    evalPanValueExp, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    structuredNoFfi, bindPanValueParameters, assignPanValueCallResult,
    updatePanValueMap, lookupPanFunction]

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
    isWfShape.isWfShapeList,
    evalPanValueExps, evalPanValueExp.evalPanValueExps,
    structuredNoFfi, updatePanValueMap, updatePanValueMemory,
    panValueShape, panShapeMatches]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) [] [] structuredNoFfi
      0 100 8 5 (fun _ => none) (fun _ => none) (fun _ => none)
      (.while (.const 0) (.break))).map
      (fun result => match result with
        | .normal _ _ _ => true
        | _ => false) = some true := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueExp,
    structuredNoFfi]

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
