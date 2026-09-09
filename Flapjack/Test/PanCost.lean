import Flapjack.PanCost

namespace Flapjack

def panCostTestPrimitive : PanPrimitiveHandler Nat := fun _ _ => none
def panCostTestFfi : PanValueFfiHandler Nat := fun _ _ _ _ _ locals => some locals
def panCostTestMemory : Nat → Option (PanValue Nat) := fun _ => none

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] [] 0 100 1 20
    (fun _ => none) (fun _ => none) panCostTestMemory
    (.seq
      (.store (.const 10) (.rStruct [.const 3, .const 5]))
      (.return (.load (.comb [.one, .one]) (.const 10))))).map
      (fun (result, cost) => match result with
        | .returned _ _ _ [PanValue.rStruct [PanValue.word 3, PanValue.word 5]] =>
            cost.steps == 9 && cost.maxCallDepth == 0 && cost.maxStoreAddress == some 11
        | _ => false) = some true

def panCostTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] panCostTestFunctions
    0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map
      (fun (result, cost) => match result with
        | .returned _ _ _ [PanValue.word 41] =>
            cost.steps == 4 && cost.maxCallDepth == 1 && cost.maxStoreAddress.isNone
        | _ => false) = some true

def panCostReturned41 : PanValueControlResult Nat → Bool
  | .returned _ _ _ [PanValue.word 41] => true
  | _ => false

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] panCostTestFunctions
    0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map (fun (result, _) => panCostReturned41 result) =
  (evalPanValueProgWithPrimitiveCallsAndFfi panCostTestPrimitive panCostTestFfi []
    panCostTestFunctions 0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map panCostReturned41

end Flapjack
