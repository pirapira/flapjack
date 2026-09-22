import Flapjack.Pancake.PanStatic

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

/-! Cake's `Skip` is an ordinary fall-through statement: unlike `Tick` and
    `Annot`, it returns `OtherLast` (`panStaticScript.sml:1049-1055`). -/
def staticProgSkipMetadataOracle : Bool :=
  match staticProgCheck (.skip : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgSkipMetadataOracle

def staticProgCallContext : Context :=
  { staticProgParityContext with
    functions := [("callee", { returnShape := .one, params := [] }),
      ("f", { returnShape := .one, params := [] })] }

def staticProgReturnContext : Context :=
  { staticProgParityContext with
    functions := [("f", { returnShape := .one, params := [] })] }

def staticProgCallCheck (program : Prog Nat) : StaticResult ProgReturn :=
  checkProg staticProgCallContext program

def staticProgDeltaContext : Context :=
  { staticProgCallContext with
    locals := ("x", { shapedBased := .word .trusted }) :: staticProgCallContext.locals }

def staticProgDeltaCheck (program : Prog Nat) : StaticResult ProgReturn :=
  checkProg staticProgDeltaContext program

def staticProgDeltaHas (program : Prog Nat) (name : String)
    (expected : ShapedBased) : Bool :=
  match (staticProgDeltaCheck program).1 with
  | Except.ok result =>
      match lookupInfo name result.variableDelta with
      | some info => info.shapedBased == expected
      | none => false
  | Except.error _ => false

def staticProgDeltaRemovesDeclaration : Bool :=
  match (staticProgDeltaCheck
      (.dec "y" .one (.const 0) (.assign .local "x" (.const 1)))).1 with
  | (Except.ok result) =>
      (lookupInfo "y" result.variableDelta).isNone &&
        (lookupInfo "x" result.variableDelta).isSome
  | (Except.error _) => false

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
  match checkProg staticProgReturnContext
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

/-! A declared exception with a matching structured payload exits the current
    function in Cake, with `RaiseLast` and no local delta or diagnostics. -/
def staticProgRaiseMetadataOracle : Bool :=
  match staticProgCheck
      (.raise "E" (.rStruct [.const 0, .const 1])) with
  | (Except.ok result, warnings) =>
      result.exitsFunction && !result.exitsLoop && result.last == .raiseLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgRaiseMetadataOracle

/-! Cake warns when a local store address is a word but is not calculated
    from the base address.  `bytesInWord` is the executable NotBased case. -/
def staticProgLocalStoreWarningOracle : Bool :=
  match staticProgCheck (.store .bytesInWord (.const 0)) with
  | (Except.ok result, [StatErr.warning message]) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        message == "L: local store address is not calculated from base in function f\n"
  | _ => false

#guard staticProgLocalStoreWarningOracle

/- Cake logs the local-store basedness warning before rejecting an invalid
   Store32 value (`panStaticScript.sml:1580-1610`). -/
#guard
  match staticProgCheck
      (.store32 .bytesInWord (.rStruct [.const 0])) with
  | (Except.error (.shape message), [StatErr.warning warning]) =>
      message == "L: store value has shape {1} instead of a word in function f\n" &&
        warning == "L: local store address is not calculated from base in function f\n"
  | _ => false

/- The same warning-before-value-shape rule applies to shared stores. -/
#guard
  match staticProgCheck
      (.shMemStore .opW .baseAddr (.rStruct [.const 0])) with
  | (Except.error (.shape message), [StatErr.warning warning]) =>
      message == "L: store value has shape {1} instead of a word in function f\n" &&
        warning == "L: shared store address is calculated from base in function f\n"
  | _ => false

/- StoreByte follows the same warning-before-value-shape rule. -/
#guard
  match staticProgCheck
      (.storeByte .bytesInWord (.rStruct [.const 0])) with
  | (Except.error (.shape message), [StatErr.warning warning]) =>
      message == "L: store value has shape {1} instead of a word in function f\n" &&
        warning == "L: local store address is not calculated from base in function f\n"
  | _ => false

/- Cake evaluates the value expression before rejecting a non-word address. -/
#guard
  staticResultErrorMessage (staticProgCheck
      (.store32 (.rStruct [.const 0]) (.var .local "missing"))) ==
    some "L: variable missing is not in scope in function f\n"

/-! Cake's ExtCall checks all four FFI words and otherwise returns ordinary
    fall-through metadata without a warning. -/
def staticProgExtCallMetadataOracle : Bool :=
  match staticProgCheck
      (.extCall "ffi" (.const 0) (.const 1) (.const 2) (.const 3)) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgExtCallMetadataOracle

/-! Cake warns when a shared store address is calculated from the base
    address.  `baseAddr` is the executable Based case for this branch. -/
def staticProgSharedStoreWarningOracle : Bool :=
  match staticProgCheck (.shMemStore .opW .baseAddr (.const 0)) with
  | (Except.ok result, [StatErr.warning message]) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        message == "L: shared store address is calculated from base in function f\n"
  | _ => false

#guard staticProgSharedStoreWarningOracle

def staticProgWordLocalContext : Context :=
  { staticProgParityContext with
    locals := ("x", { shapedBased := .word .trusted }) :: staticProgParityContext.locals }

/-! Cake's If merges branch deltas with branch_loc_inf; a local changed in
    only one branch becomes NotTrusted against the incoming local. -/
def staticProgIfDeltaOracle : Bool :=
  match checkProg staticProgWordLocalContext
      (.ite (.const 1) (.assign .local "x" (.const 0)) .skip) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .notTrusted
        | none => false
  | _ => false

#guard staticProgIfDeltaOracle

/-! Cake's Seq returns the union of the first and second local deltas; a
    transparent second statement must not erase the first assignment. -/
def staticProgSeqDeltaOracle : Bool :=
  match checkProg staticProgWordLocalContext
      (.seq (.assign .local "x" (.const 0)) .skip) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .notBased
        | none => false
  | _ => false

#guard staticProgSeqDeltaOracle

/-! Cake's While retains the body's local delta, merged against the
    surrounding locals and the empty second branch of its synthetic If. -/
def staticProgWhileDeltaOracle : Bool :=
  match checkProg staticProgWordLocalContext
      (.while (.const 1) (.assign .local "x" (.const 0))) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .notTrusted
        | none => false
  | _ => false

#guard staticProgWhileDeltaOracle

/-! Cake's local shared-memory load both warns on a Base address and records
    the loaded word in the local variable delta as Trusted. -/
def staticProgLocalLoadMetadataOracle : Bool :=
  match checkProg staticProgWordLocalContext
      ((.shMemLoad .opW .local "x" .baseAddr) : Prog Nat) with
  | (Except.ok result, [StatErr.warning message]) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " &&
        message == "L: shared load address is calculated from base in function f\n" &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .trusted
        | none => false
  | _ => false

#guard staticProgLocalLoadMetadataOracle

/- Cake retains a based-address warning before rejecting a non-word load
   destination (`panStaticScript.sml:1642-1706`). -/
#guard
  match checkProg staticProgParityContext
      ((.shMemLoad .opW .local "pair" .baseAddr) : Prog Nat) with
  | (Except.error (.shape message), [StatErr.warning warning]) =>
      message == "L: load variable has shape {1,1} instead of a word in function f\n" &&
        warning == "L: shared load address is calculated from base in function f\n"
  | _ => false

/- The same address-before-destination sequencing applies to global loads. -/
#guard
  match checkProg staticProgParityContext
      ((.shMemLoad .opW .global "g" .baseAddr) : Prog Nat) with
  | (Except.error (.shape message), [StatErr.warning warning]) =>
      message == "L: load variable has shape {1,1} instead of a word in function f\n" &&
        warning == "L: shared load address is calculated from base in function f\n"
  | _ => false

/-! Cake's call with no destination is a tail call: matching caller/callee
    return shapes produce TailLast and function exit metadata. -/
def staticProgTailCallMetadataOracle : Bool :=
  match staticProgCallCheck (.call none "callee" []) with
  | (Except.ok result, warnings) =>
      result.exitsFunction && !result.exitsLoop && result.last == .tailLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgTailCallMetadataOracle

def staticProgWordLocalCallContext : Context :=
  { staticProgCallContext with
    locals := ("x", { shapedBased := .word .trusted }) :: staticProgCallContext.locals }

def staticProgGlobalHandlerContext : Context :=
  { staticProgCallContext with
    globals := [("g", { shape := .one })]
    locals := ("h", { shapedBased := .word .notBased }) :: staticProgCallContext.locals }

/-! Cake promotes a global-call handler variable to Trusted before checking
    its body; using it as a store address therefore emits no basedness warning. -/
def staticProgGlobalHandlerTrustOracle : Bool :=
  match checkProg staticProgGlobalHandlerContext
      ((.call
        (some (some (.global, "g"), some ("Missing", "h",
          (.store (.var .local "h") (.const 0))))) "callee" []) : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgGlobalHandlerTrustOracle

def staticProgInvalidHandlerShapeContext : Context :=
  { staticProgCallContext with
    exceptions := [("E", .named "Missing")]
    locals := ("h", { shapedBased := .named "Missing" [] }) ::
      staticProgCallContext.locals }

/-! Cake rejects a handler whose already-accepted exception shape cannot be
    converted to shaped basedness in the current structure context. -/
#guard
  staticResultErrorMessage
      (checkProg staticProgInvalidHandlerShapeContext
        ((.call (some (none, some ("E", "h", .skip))) "callee" []) : Prog Nat)) ==
    some ("L: static analysis failed to convert in-scope shape in function f\n" ++
      "this should never happen. please report to a compiler developer\n")

/- Cake's global-destination call branch does not produce a local delta and
   checks the destination shape before accepting the ordinary fall-through
   result (`panStaticScript.sml:1235-1269`). -/
def staticProgGlobalCallMetadataOracle : Bool :=
  match checkProg staticProgGlobalHandlerContext
      ((.call (some (some (.global, "g"), none)) "callee" []) : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgGlobalCallMetadataOracle

def staticProgStandaloneHandlerContext : Context :=
  { staticProgGlobalHandlerContext with
    locals :=
      ("h", { shapedBased := .struct [.word .notBased, .word .notBased] }) ::
        staticProgGlobalHandlerContext.locals }

/- Cake's standalone handled-call branch checks the declared exception and
   handler shape, trusts the handler variable while checking its body, and
   returns ordinary fall-through metadata with no destination delta
   (`panStaticScript.sml:1353-1406`). -/
def staticProgStandaloneHandlerMetadataOracle : Bool :=
  match checkProg staticProgStandaloneHandlerContext
      ((.call (some (none, some ("E", "h", .skip))) "callee" []) : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgStandaloneHandlerMetadataOracle

/- The handler-shape diagnostic is observable and must precede handler-body
   checking for a standalone call. -/
#guard
  staticResultErrorMessage
      (checkProg staticProgGlobalHandlerContext
        ((.call (some (none, some ("E", "h", .skip))) "callee" []) : Prog Nat)) ==
    some "handler variable h does not match shape of exception E\n"

def staticProgBadLocalCallDestinationContext : Context :=
  { staticProgCallContext with
    locals := ("x", { shapedBased := .struct [.word .trusted, .word .trusted] }) ::
      staticProgCallContext.locals }

/-! Cake validates a handled call's destination before its handler; the
    destination shape error therefore wins over a missing exception. -/
#guard
  staticResultErrorMessage (checkProg staticProgBadLocalCallDestinationContext
      ((.call
        (some (some (.local, "x"), some ("Missing", "h", .skip)))
        "callee" []) : Prog Nat)) ==
    some "L: result of function call callee assigned to local variable x has shape 1 instead of declared shape {1,1} in function f\n"

/-! Cake checks a destination's scope before the callee.  These conflicting
    cases preserve the destination diagnostic even when the function is
    unknown. -/
#guard
  staticResultErrorMessage (checkProg staticProgCallContext
      ((.call (some (some (.local, "missing"), none)) "Unknown" []) : Prog Nat)) ==
    some "L: variable missing is not in scope in function f\n"

#guard
  staticResultErrorMessage (checkProg staticProgCallContext
      ((.call (some (some (.global, "missing"), none)) "Unknown" []) : Prog Nat)) ==
    some "L: variable missing is not in scope in function f\n"

/-! Cake's accepted local-destination call records the destination's trusted
    shape in the returned variable delta. -/
def staticProgLocalCallMetadataOracle : Bool :=
  match checkProg staticProgWordLocalCallContext
      ((.call (some (some (.local, "x"), none)) "callee" []) : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .trusted
        | none => false
  | _ => false

#guard staticProgLocalCallMetadataOracle

/-! Cake's DecCall removes only its newly declared destination from the body
    delta; assignments to pre-existing locals remain observable. -/
def staticProgDecCallMetadataOracle : Bool :=
  match checkProg staticProgWordLocalCallContext
      ((.decCall "y" .one "callee" []
        (.assign .local "x" (.const 0))) : Prog Nat) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "x" result.variableDelta with
        | some info => info.shapedBased == .word .notBased
        | none => false
  | _ => false

#guard staticProgDecCallMetadataOracle

/-! Cake's accepted AddCarry primitive records its structured result shape in
    the destination delta. -/
def staticProgPrimitiveMetadataOracle : Bool :=
  match staticProgCheck
      (.primitive "pair" .addCarry [.const 0, .const 1, .const 2]) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.currentLocation == "L: " && warnings.isEmpty &&
        result.variableDelta.length == 1 &&
        match lookupInfo "pair" result.variableDelta with
        | some info =>
            info.shapedBased == .struct [.word .notBased, .word .notBased]
        | none => false
  | _ => false

#guard staticProgPrimitiveMetadataOracle

/-! Cake's Dec removes only its newly declared local from the body delta. -/
def staticProgDecMetadataOracle : Bool :=
  match staticProgCheck
      (.dec "x" .one (.const 0) (.assign .local "x" (.const 1))) with
  | (Except.ok result, warnings) =>
      !result.exitsFunction && !result.exitsLoop && result.last == .otherLast &&
        result.variableDelta.isEmpty && result.currentLocation == "L: " &&
        warnings.isEmpty
  | _ => false

#guard staticProgDecMetadataOracle

/-! Cake's sequence rule keeps the first function exit flag, but `Skip` is an
    ordinary `OtherLast` statement, so `seq_last_stmt` returns `OtherLast`.
    Check the returned metadata, not only the acceptance/error bit. -/
def staticProgReturnMetadataOracle : Bool :=
  match checkProg staticProgReturnContext (.seq (.return (.const 0)) .skip) with
  | (Except.ok result, warnings) =>
      result.exitsFunction && !result.exitsLoop &&
        result.last == .otherLast && result.variableDelta.isEmpty &&
        result.currentLocation == "L: " &&
        match warnings with
        | [StatErr.warning message] =>
            message == "L: unreachable statement(s) after return in function f\n"
        | _ => false
  | _ => false

#guard staticProgReturnMetadataOracle

/-! Cake rejects Return outside a FunScope with its implementation error. -/
#guard
  match checkProg
      { staticProgParityContext with scope := .topLevel, expectedReturn := none }
      (.return (.const 0)) with
  | (Except.error (.general _), []) => true
  | _ => false

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
  staticResultErrorMessage (checkProg staticProgReturnContext
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

/-! Cake's `var_delta` is observable to the following checker node.  These
    guards cover local assignment, sequential composition, branch merging,
    loop merging, call destinations, declarations, and shared-memory loads. -/
#guard staticProgDeltaHas (.assign .local "x" (.const 1)) "x" (.word .notBased)

#guard staticProgDeltaHas
  (.seq (.assign .local "x" (.const 1)) .skip) "x" (.word .notBased)

#guard staticProgDeltaHas
  (.ite (.const 1)
    (.assign .local "x" (.const 1))
    (.assign .local "x" (.const 2))) "x" (.word .notBased)

#guard staticProgDeltaHas
  (.while (.const 1) (.assign .local "x" (.const 1))) "x" (.word .notTrusted)

#guard staticProgDeltaHas
  (.call (some (some (.local, "x"), none)) "callee" []) "x" (.word .trusted)

#guard staticProgDeltaHas
  (.shMemLoad .opW .local "x" (.const 0)) "x" (.word .trusted)

#guard staticProgDeltaRemovesDeclaration

end Flapjack
