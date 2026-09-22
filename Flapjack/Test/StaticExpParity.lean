import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for the error and sequencing behavior in CakeML's
    `static_check_exp_def` (`cakeml/pancake/panStaticScript.sml:806-1001`). -/

def staticExpParityContext : Context :=
  { locals :=
      [("pair", { shapedBased := .struct [.word .trusted, .word .trusted] })]
    globals := []
    functions := []
    expectedReturn := none
    exceptions := []
    structs := [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
    scope := .funScope "f" ""
    inLoop := false
    reachable := .isReach
    last := .invisLast
    location := "L: " }

def staticExpCheck (expression : Exp Nat) : StaticResult ExpReturn :=
  checkExp staticExpParityContext expression

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.rField 2 (.var .local "pair"))) ==
    some "L: expression shape {1,1} has no field at index 2 in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck (.nStruct "Missing" [])) ==
    some "L: struct name Missing is not in scope in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.nField "missing" (.var .local "pair"))) ==
    some "L: expression shape {1,1} has no field missing in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.load (.named "Missing") (.const 0))) ==
    some "L: struct name Missing is not in scope in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.load .one (.rStruct [.const 0]))) ==
    some "L: load address has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck (.op .add [.const 0])) ==
    some "L: operation Add requires at least 2 operands, 1 provided in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.op .add [.var .local "pair", .const 0])) ==
    some "L: operation Add operand has shape {1,1} instead of a word in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck (.panOp .mul [.const 0])) ==
    some "L: operation Mul only accepts 2 operands, 1 provided in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.cmp .equal (.const 0) (.rStruct [.const 0]))) ==
    some "L: comparison given operands of different shapes in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.shift .lsl (.rStruct [.const 0]) (.const 0))) ==
    some "L: shifted expression has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage
      (staticExpCheck
        (.shift .lsl (.const 0) (.rStruct [.const 0]))) ==
    some "L: shift expression has shape {1} instead of a word in function f\n"

end Flapjack
