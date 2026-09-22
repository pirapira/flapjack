import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_func_args_def`
    (`cakeml/pancake/panStaticScript.sml:690-718`). -/

def funcArgsParityContext : Context :=
  { locals := []
    globals := []
    functions := []
    expectedReturn := none
    exceptions := []
    structs := []
    scope := .funScope "caller" ""
    inLoop := false
    reachable := .isReach
    last := .invisLast
    location := "line: " }

#guard
  staticResultOk
      (checkFuncArgs funcArgsParityContext "f" [("x", .one)]
        [.word .notBased])

#guard
  staticResultErrorMessage
      (checkFuncArgs funcArgsParityContext "f" [("x", .one)] []) ==
    some "line: argument x for call to function f is missing in function caller\n"

#guard
  staticResultErrorMessage
      (checkFuncArgs funcArgsParityContext "f" [] [.word .trusted]) ==
    some "line: extra arguments given to function f in function caller\n"

#guard
  staticResultErrorMessage
      (checkFuncArgs funcArgsParityContext "f" [("x", .one)]
        [.struct [.word .trusted]]) ==
    some "line: value for argument x given to function f has shape {1} instead of declared shape 1 in function caller\n"

end Flapjack
