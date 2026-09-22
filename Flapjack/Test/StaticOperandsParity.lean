import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_operands_def`
    (`cakeml/pancake/panStaticScript.sml:660-671`). -/

def operandsParityContext : Context :=
  { locals := []
    globals := []
    functions := []
    expectedReturn := none
    exceptions := []
    structs := []
    scope := .funScope "f" ""
    inLoop := false
    reachable := .isReach
    last := .invisLast
    location := "line: " }

#guard
  match checkOperands operandsParityContext "AddCarry" [] with
  | (.ok .notBased, []) => true
  | _ => false

#guard
  match checkOperands operandsParityContext "AddCarry"
      [.word .trusted, .word .notBased, .word .based] with
  | (.ok .based, []) => true
  | _ => false

#guard
  staticResultErrorMessage
      (checkOperands operandsParityContext "AddCarry"
        [.word .trusted, .struct [.word .notBased]]) ==
    some "line: operation AddCarry operand has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage
      (checkPrimitiveArgs operandsParityContext .addCarry
        [.word .trusted, .word .notBased]) ==
    some "line: operation AddCarry only accepts 3 operands, 2 provided in function f\n"

end Flapjack
