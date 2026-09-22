import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_struct_fields_def`
    (`cakeml/pancake/panStaticScript.sml:717-765`). -/

def structFieldsParityContext : Context :=
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

def pairFields : List (FieldName × Shape) :=
  [("left", .one), ("right", .one)]

#guard
  staticResultOk
      (checkStructFields structFieldsParityContext "Pair" pairFields
        [("left", .word .notBased), ("right", .word .trusted)])

#guard
  staticResultErrorMessage
      (checkStructFields structFieldsParityContext "Pair" pairFields
        [("left", .word .notBased)]) ==
    some "line: missing field right in named struct Pair constant in function f\n"

#guard
  staticResultErrorMessage
      (checkStructFields structFieldsParityContext "Pair" pairFields
        [("left", .word .notBased), ("left", .word .trusted),
         ("right", .word .trusted)]) ==
    some "line: multiple values for field left in named struct Pair constant in function f\n"

#guard
  staticResultErrorMessage
      (checkStructFields structFieldsParityContext "Pair" pairFields
        [("left", .word .notBased), ("right", .word .trusted),
         ("extra", .word .trusted)]) ==
    some "line: unexpected field extra given to named struct Pair in function f\n"

#guard
  staticResultErrorMessage
      (checkStructFields structFieldsParityContext "Pair" pairFields
        [("left", .struct [.word .trusted]), ("right", .word .trusted)]) ==
    some "line: value for field left given to named struct Pair has shape {1} instead of declared shape 1 in function f\n"

end Flapjack
