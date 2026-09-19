import Flapjack.Static

namespace Flapjack

/-! Direct executable parity for representative branches of CakeML's
    `static_check_prog_def` (`cakeml/pancake/panStaticScript.sml:1100-1740`). -/

def staticProgParityContext : Context :=
  { locals :=
      [("pair", { shapedBased := .struct [.word .trusted, .word .trusted] })]
    globals := [("g", { shape := .comb [.one, .one] })]
    functions := []
    expectedReturn := some .one
    exceptions := [("E", .comb [.one, .one])]
    structs := [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
    scope := .funScope "f" ""
    inLoop := false
    reachable := .isReach
    last := .invisLast
    location := "L: " }

def staticProgCheck (program : Prog Nat) : StaticResult ProgReturn :=
  checkProg staticProgParityContext program

def staticProgCallContext : Context :=
  { staticProgParityContext with
    functions := [("callee", { returnShape := .one, params := [] })] }

def staticProgCallCheck (program : Prog Nat) : StaticResult ProgReturn :=
  checkProg staticProgCallContext program

#guard
  staticResultErrorMessage (staticProgCheck
      (.dec "x" (.named "Missing") (.const 0) .skip)) ==
    some "L: struct name Missing is not in scope in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.dec "x" (.comb [.one, .one]) (.const 0) .skip)) ==
    some "L: expression to initialise local variable x has shape 1 instead of declared shape {1,1} in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.assign .local "pair" (.const 0))) ==
    some "L: expression assigned to local variable pair has shape 1 instead of declared shape {1,1} in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.assign .global "g" (.const 0))) ==
    some "L: expression assigned to global variable g has shape 1 instead of declared shape {1,1} in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.store (.rStruct [.const 0]) (.const 0))) ==
    some "L: store address has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.store32 (.const 0) (.rStruct [.const 0]))) ==
    some "L: store value has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.ite (.rStruct [.const 0]) .skip .skip)) ==
    some "L: if condition has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.while (.rStruct [.const 0]) .skip)) ==
    some "L: while condition has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck .break) ==
    some "L: break statement outside loop in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.raise "Missing" (.const 0))) ==
    some "exception Missing is not declared\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.raise "E" (.const 0))) ==
    some "raised exception E has wrong value shape\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.return (.rStruct [.const 0]))) ==
    some "L: expression to return has shape {1} instead of declared shape 1 in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.extCall "ffi" (.rStruct [.const 0]) (.const 0) (.const 0) (.const 0))) ==
    some "L: value for argument given to FFI ffi has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.shMemLoad .opW .local "pair" (.const 0))) ==
    some "L: load variable has shape {1,1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCheck
      (.shMemStore .opW (.rStruct [.const 0]) (.const 0))) ==
    some "L: store address has shape {1} instead of a word in function f\n"

#guard
  staticResultErrorMessage (staticProgCallCheck
      (.call (some (some (.local, "pair"), none)) "callee" [])) ==
    some "L: result of function call callee assigned to local variable pair has shape 1 instead of declared shape {1,1} in function f\n"

#guard
  staticResultErrorMessage (staticProgCallCheck
      (.decCall "x" (.comb [.one, .one]) "callee" [] .skip)) ==
    some "L: result of function call callee to initialise local variable x has shape 1 instead of declared shape {1,1} in function f\n"

end Flapjack
