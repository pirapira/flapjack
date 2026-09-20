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

def staticProgLoopControlContext : Context :=
  { staticProgParityContext with inLoop := true }

/-! Cake returns loop exits as intermediate metadata: both controls exit the
    loop, preserve the current location, and carry no variable delta. -/
def staticProgLoopControlMetadataOracle : Bool :=
  let checkControl := fun (program : Prog Nat) (expected : LastStmt) =>
    match checkProg staticProgLoopControlContext program with
    | (Except.ok result, warnings) =>
        !result.exitsFunction && result.exitsLoop && result.last == expected &&
          result.variableDelta.isEmpty && result.currentLocation == "L: " &&
          warnings.isEmpty
    | _ => false
  checkControl .break .breakLast && checkControl .continue .contLast

#guard staticProgLoopControlMetadataOracle

/-! Cake's `If` combines branch exits conjunctively and selects the
    branch-specific terminal marker only when both branches exit. -/
def staticProgIfMetadataOracle : Bool :=
  match staticProgCheck
      (.ite (.const 1) (.return (.const 0)) (.return (.const 0))) with
  | (Except.ok result, warnings) =>
      result.exitsFunction && !result.exitsLoop && result.last == .condExitLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgIfMetadataOracle

/-! Cake's `While` consumes loop-control exits from its body: the enclosing
    result is non-exiting with `OtherLast` and a delta filtered against the
    outer locals. -/
def staticProgWhileMetadataOracle : Bool :=
  match staticProgCheck (.while (.const 1) .break) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgWhileMetadataOracle

/-! Cake's sequence rule keeps the first function exit when the second
    statement is transparent.  Check the returned metadata, not only the
    acceptance/error bit, for a return followed by Skip. -/
def staticProgReturnMetadataOracle : Bool :=
  match staticProgCheck (.seq (.return (.const 0)) .skip) with
  | (Except.ok result, warnings) =>
      result.exitsFunction && !result.exitsLoop &&
        result.last == .retLast && result.variableDelta.isEmpty &&
        result.currentLocation == "L: " &&
        match warnings with
        | [StatErr.warning message] =>
            message == "L: unreachable statement(s) after return in function f\n"
        | _ => false
  | _ => false

#guard staticProgReturnMetadataOracle

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
