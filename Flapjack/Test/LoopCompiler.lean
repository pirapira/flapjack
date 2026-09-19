import Flapjack.Test.Calls

namespace Flapjack

open RiscV

/-! Cake's `get_eids_from_decls` numbers only exception declarations; ordinary
    functions and globals do not consume exception identifiers.  This matters
    for the source entry wrapper, which precedes the declarations passed to the
    Crepe context. -/
def exceptionNumberingFixture : List (Decl Nat) :=
  [.function
      { name := "before", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
   .exnDecl "E" .one,
   .function
      { name := "between", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
   .exnDecl "F" .one]

#guard
  crepGetEidsFromDecls (fun value => value) exceptionNumberingFixture ==
    [("E", 0), ("F", 1)]

#guard
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.while (.const (BitVec.ofNat 64 0)) .break)
            (.return (.const (BitVec.ofNat 64 7))), returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 7]

#guard
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.store (.const (BitVec.ofNat 64 100))
              (.const (BitVec.ofNat 64 42)))
            (.return (.load .one (.const (BitVec.ofNat 64 100)))),
          returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 42]

#guard
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .ite (.cmp .equal (.const (BitVec.ofNat 64 1))
            (.const (BitVec.ofNat 64 1)))
            (.return (.const (BitVec.ofNat 64 7)))
            (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome)

#guard
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome)

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  decide +kernel

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  decide +kernel

example :
    let result := compileFlapjackCore (α := Nat) .rv64i 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.globals.initializers.length = 1 ∧ result.crepe.length = 1 := by
  simp [compileFlapjackCore, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers, pipelineInlineNames,
    compileToCrep, compileFunctionsSource, compileFunDeclSource,
    crepInlineTopRecursiveByNames, crepInlineTopRecursive,
    crepInlineFunctionsRecursive, crepInlineActiveNames,
    crepSimpFunctions
    ]

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  decide +kernel

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.rStruct []), returnShape := .one }]) = false := by
  decide +kernel

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  decide +kernel

example :
    (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .seq (.return (.const 7)) .skip, returnShape := .one }]).2.length = 1 := by
  decide +kernel

/-! Cake's reachability-warning equations. `Annot` and `Tick` are transparent
    to `reached_warnable`, while an exiting statement moves the next ordinary
    node to `WarnReach`; the production sequence case below consumes these
    equations for both function and loop exits. -/
def reachabilityContext : Context :=
  { locals := [], globals := [], functions := [], expectedReturn := some .one,
    exceptions := [], structs := [], scope := .funScope "f" "", inLoop := false,
    reachable := .isReach, last := .otherLast, location := "" }

#guard nextIsReachable .isReach .retLast == .warnReach
#guard nextIsReachable .isReach .breakLast == .warnReach
#guard nextIsReachable .isReach .invisLast == .isReach
#guard
  nextIsReachable .isReach .raiseLast == .warnReach &&
  nextIsReachable .isReach .tailLast == .warnReach &&
  nextIsReachable .isReach .contLast == .warnReach &&
  nextIsReachable .isReach .condExitLast == .warnReach &&
  nextIsReachable .isReach .otherLast == .isReach &&
  nextIsReachable .isReach .invisLast == .isReach &&
  nextIsReachable .warnReach .retLast == .warnReach &&
  nextIsReachable .notReach .retLast == .notReach
#guard
  nextNowUnreachable .isReach .isReach == false &&
  nextNowUnreachable .isReach .warnReach == true &&
  nextNowUnreachable .isReach .notReach == true &&
  nextNowUnreachable .warnReach .isReach == false &&
  nextNowUnreachable .warnReach .warnReach == false &&
  nextNowUnreachable .warnReach .notReach == false &&
  nextNowUnreachable .notReach .isReach == false &&
  nextNowUnreachable .notReach .warnReach == false &&
  nextNowUnreachable .notReach .notReach == false
#guard
  (reachedWarnable (.seq (.skip : Prog Nat) .skip)
    { reachabilityContext with reachable := .warnReach, last := .retLast }).1.isNone &&
  (reachedWarnable (.tick : Prog Nat)
    { reachabilityContext with reachable := .warnReach, last := .retLast }).1.isNone &&
  (reachedWarnable (.annot "" "" : Prog Nat)
    { reachabilityContext with reachable := .warnReach, last := .retLast }).1.isNone &&
  (reachedWarnable (.return (.const 1) : Prog Nat)
    { reachabilityContext with reachable := .warnReach, last := .retLast }).1 ==
      some .retLast &&
  (reachedWarnable (.return (.const 1) : Prog Nat)
    { reachabilityContext with reachable := .warnReach, last := .retLast }).2.reachable ==
      .notReach &&
  (reachedWarnable (.return (.const 1) : Prog Nat) reachabilityContext).1.isNone &&
  (reachedWarnable (.return (.const 1) : Prog Nat) reachabilityContext).2.reachable ==
      .isReach
#guard (reachedWarnable (.annot "" "" : Prog Nat) reachabilityContext).1.isNone
#guard (reachedWarnable (.tick : Prog Nat) reachabilityContext).1.isNone
#guard (reachedWarnable (.skip : Prog Nat)
  { reachabilityContext with reachable := .warnReach, last := .breakLast }).1 ==
    some .breakLast
#guard seqLastStmt .retLast .invisLast == .retLast
#guard staticLastStmtString .breakLast == "break"

/-! Direct Cake `last_to_str_def` parity
    (`cakeml/pancake/panStaticScript.sml:359-367`).  These strings are used
    only by warning diagnostics, but their exact spellings are observable. -/
#guard staticLastStmtString .retLast == "return" &&
  staticLastStmtString .raiseLast == "raise" &&
  staticLastStmtString .tailLast == "tail call" &&
  staticLastStmtString .breakLast == "break" &&
  staticLastStmtString .contLast == "continue" &&
  staticLastStmtString .condExitLast == "exiting conditional" &&
  staticLastStmtString .invisLast == "" &&
  staticLastStmtString .otherLast == ""

#guard match basedMerge .based .notBased with | .based => true | _ => false
#guard match basedMerge .trusted .notBased with | .trusted => true | _ => false
#guard match shapedBasedMerge [.word .based, .word .notBased] with
  | .based => true | _ => false

/-! Direct Cake `based_merge` parity (`panStaticScript.sml:288-298`). -/
#guard match basedMerge .notBased .notBased with
  | .notBased => true | _ => false
#guard match basedMerge .trusted .notBased with
  | .trusted => true | _ => false
#guard match basedMerge .notBased .trusted with
  | .trusted => true | _ => false
#guard match basedMerge .notTrusted .trusted with
  | .notTrusted => true | _ => false
#guard match basedMerge .trusted .notTrusted with
  | .notTrusted => true | _ => false
#guard match basedMerge .based .notTrusted with
  | .based => true | _ => false
#guard match basedMerge .notTrusted .based with
  | .based => true | _ => false

/-! Direct Cake `sh_bd_branch` parity (`panStaticScript.sml:301-305`). -/
#guard match shapedBasedBranch (.word .trusted) (.word .trusted) with
  | .word .trusted => true | _ => false
#guard match shapedBasedBranch (.word .trusted) (.word .notBased) with
  | .word .notTrusted => true | _ => false
#guard match shapedBasedBranch
    (.struct [.word .trusted, .word .based])
    (.struct [.word .trusted, .word .notBased]) with
  | .struct [.word .notTrusted, .word .notTrusted] => true | _ => false
#guard match shapedBasedBranch
    (.named "Pair" [("left", .word .trusted)])
    (.named "Pair" [("left", .word .trusted)]) with
  | .named "Pair" [("left", .word .trusted)] => true | _ => false

/-! Direct Cake `branch_loc_inf` parity (`panStaticScript.sml:311-334`). -/
#guard
  match branchLocInf
      [("x", { shapedBased := .word .trusted })]
      [("x", { shapedBased := .word .trusted })] [] with
  | [("x", { shapedBased := .word .trusted })] => true
  | _ => false
#guard
  match branchLocInf
      [("x", { shapedBased := .word .notBased })]
      [("x", { shapedBased := .word .trusted })] [] with
  | [("x", { shapedBased := .word .notTrusted })] => true
  | _ => false
#guard
  match branchLocInf [] []
      [("y", { shapedBased := .struct [.word .trusted, .word .based] })] with
  | [("y", { shapedBased := .struct [.word .notTrusted, .word .notTrusted] })] => true
  | _ => false
#guard
  match branchLocInf []
      [("x", { shapedBased := .word .trusted })]
      [("x", { shapedBased := .word .notBased }),
       ("y", { shapedBased := .word .based })] with
  | [("x", { shapedBased := .word .notTrusted }),
     ("y", { shapedBased := .word .notTrusted })] => true
  | _ => false

/-! Direct Cake `seq_loc_inf` parity (`panStaticScript.sml:337-338`). -/
#guard
  match seqLocInf
      [("x", { shapedBased := .word .trusted })]
      [("x", { shapedBased := .word .based })] with
  | [("x", { shapedBased := .word .based })] => true
  | _ => false
#guard
  match seqLocInf
      [("x", { shapedBased := .word .trusted })]
      [("y", { shapedBased := .word .based })] with
  | [("y", { shapedBased := .word .based }),
     ("x", { shapedBased := .word .trusted })] => true
  | _ => false

/-! Direct Cake `sh_bd_to_str` parity (`panStaticScript.sml:342-350`). -/
#guard shapedBasedToString (.word .trusted) == "1"
#guard shapedBasedToString (.struct []) == "{}"
#guard shapedBasedToString
    (.struct [.word .based, .struct [.word .notTrusted, .word .trusted]]) ==
    "{1,{1,1}}"
#guard shapedBasedToString
    (.named "Pair" [("left", .word .trusted), ("right", .word .based)]) == "Pair"

/-! Direct Cake `sh_bd_from_sh` parity (`panStaticScript.sml:213-233`).
    The explicit basedness must reach every word in comb and named shapes. -/
#guard match shapedBasedFromShapeWith [] .based .one with
  | some (.word .based) => true | _ => false
#guard match shapedBasedFromShapeWith [] .notTrusted (.comb [.one, .one]) with
  | some (.struct [.word .notTrusted, .word .notTrusted]) => true | _ => false
#guard
  let context : StructContext :=
    [("Pair", StructInfo.mk [("lo", .one), ("hi", .one)] 2
      [("lo", .word .trusted), ("hi", .word .trusted)])]
  match shapedBasedFromShapeWith context .based (.named "Pair") with
  | some (.named "Pair" [("lo", .word .based), ("hi", .word .based)]) => true
  | _ => false

/-! Direct Cake `sh_bd_from_bd` parity (`panStaticScript.sml:236-240`). -/
#guard match shapedBasedWithBase .based (.word .notBased) with
  | .word .based => true | _ => false
#guard match shapedBasedWithBase .notTrusted
    (.struct [.word .based, .struct [.word .trusted]]) with
  | .struct [.word .notTrusted, .struct [.word .notTrusted]] => true
  | _ => false
#guard match shapedBasedWithBase .trusted
    (.named "Pair" [("lo", .word .based), ("hi", .word .notBased)]) with
  | .named "Pair" [("lo", .word .trusted), ("hi", .word .trusted)] => true
  | _ => false

/-! Direct Cake `sh_bd_has_shape` parity (`panStaticScript.sml:244-258`). -/
#guard shapedBasedHasShape .one (.word .based) == true
#guard shapedBasedHasShape .one (.struct []) == false
#guard shapedBasedHasShape (.comb [.one, .comb [.one]])
    (.struct [.word .trusted, .struct [.word .notBased]]) == true
#guard shapedBasedHasShape (.comb [.one, .one]) (.struct [.word .trusted]) == false
#guard shapedBasedHasShape (.named "Pair")
    (.named "Pair" [("ignored", .struct [])]) == true
#guard shapedBasedHasShape (.named "Pair") (.named "Other" []) == false

/-! Direct Cake `sh_bd_eq_shapes` parity (`panStaticScript.sml:259-272`). -/
#guard shapedBasedSameShape (.word .based) (.word .notBased) == true
#guard shapedBasedSameShape
    (.struct [.word .trusted, .struct [.word .based]])
    (.struct [.word .notTrusted, .struct [.word .notBased]]) == true
#guard shapedBasedSameShape (.struct [.word .trusted]) (.struct []) == false
#guard shapedBasedSameShape
    (.named "Pair" [("left", .word .based)])
    (.named "Pair" [("other", .struct [])]) == true
#guard shapedBasedSameShape (.named "Pair" []) (.named "Other" []) == false

/-! Direct Cake `index_sh_bd` parity (`panStaticScript.sml:274-279`). -/
#guard match shapedBasedFieldAt 0 (.word .based) with
  | none => true | _ => false
#guard match shapedBasedFieldAt 0
    (.struct [.word .trusted, .word .notBased]) with
  | some (.word .trusted) => true | _ => false
#guard match shapedBasedFieldAt 1
    (.struct [.word .trusted, .word .notBased]) with
  | some (.word .notBased) => true | _ => false
#guard match shapedBasedFieldAt 2
    (.struct [.word .trusted, .word .notBased]) with
  | none => true | _ => false
#guard match shapedBasedFieldAt 0 (.named "Pair" []) with
  | none => true | _ => false
#guard match shapedBasedFieldAt 0 (.struct []) with
  | none => true | _ => false

/-! Direct Cake `field_sh_bd` parity (`panStaticScript.sml:281-285`). -/
#guard match shapedBasedFieldNamed "left" (.word .based) with
  | none => true | _ => false
#guard match shapedBasedFieldNamed "left" (.struct []) with
  | none => true | _ => false
#guard match shapedBasedFieldNamed "left"
    (.named "Pair" [("left", .word .based), ("right", .word .notBased)]) with
  | some (.word .based) => true | _ => false
#guard match shapedBasedFieldNamed "missing"
    (.named "Pair" [("left", .word .based)]) with
  | none => true | _ => false
#guard match shapedBasedFieldNamed "left"
    (.named "Pair" [("left", .word .based), ("left", .word .notBased)]) with
  | some (.word .based) => true | _ => false

/-! Cake's `get_memop_msg` diagnostics (`panStaticScript.sml:491-511`) are
    directional: local operations warn about non-base addresses, while shared
    operations warn about base addresses. -/
def memoryWarningContext : Context :=
  { locals := [("notBased", { shapedBased := .word .notBased }),
      ("based", { shapedBased := .word .based })]
    globals := []
    functions := []
    expectedReturn := some .one
    exceptions := []
    structs := []
    scope := .funScope "f" ""
    inLoop := false
    reachable := .isReach
    last := .otherLast
    location := "" }

#guard
  (checkProg memoryWarningContext
    (.store (.var .local "notBased") (.const 0))).2.map statErrMessage ==
      ["local store address is not calculated from base in function f\n"]
#guard
  (checkExp memoryWarningContext
    (.load32 (.var .local "notBased") : Exp Nat)).2.map statErrMessage ==
      ["local load address is not calculated from base in function f\n"]
#guard
  (checkProg memoryWarningContext
    (.shMemStore .opW (.var .local "based") (.const 0))).2.map statErrMessage ==
      ["shared store address is calculated from base in function f\n"]
#guard
  (checkProg memoryWarningContext
    (.shMemStore .opW (.var .local "notBased") (.const 0))).2.isEmpty

#guard
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one },
       .function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 1), returnShape := .one }]) = false

/-! Cake's `check_redec_var` warns, rather than rejects, a local `Dec` that
    shadows an existing local; the warning is emitted before body warnings. -/
#guard
  (checkProg
    { reachabilityContext with
      locals := [("x", { shapedBased := .word .trusted })] }
    (.dec "x" .one (.const 0) (.skip : Prog Nat))).2.map statErrMessage ==
      ["variable x is redeclared in function f\n"]

#guard
  (checkProg
    { reachabilityContext with
      locals := [("x", { shapedBased := .word .trusted })] }
    (.decCall "x" .one "f" [] (.skip : Prog Nat))).2.map statErrMessage ==
      ["variable x is redeclared in function f\n"]

/-! A declaration resets Cake's `last` marker before checking its body, so an
    already-unreachable body's warning does not inherit the preceding return. -/
#guard
  (checkProg
    { reachabilityContext with reachable := .warnReach, last := .retLast }
    (.dec "y" .one (.const 0)
      (.seq (.skip : Prog Nat) (.return (.const 0))))).2.map statErrMessage ==
      ["unreachable statement(s) after  in function f\n"]

/-! Crepe primitives contain already-flattened variable names.  The original
    `crep_to_loop` pass resolves both sides through the loop variable map; it
    must not leave the Crepe names untouched (which can alias generated
    temporaries and makes later dead-code analysis delete live arithmetic). -/
def primitiveLoopContext : LoopContext Nat :=
  { vars := [(10, 100), (11, 101), (12, 102), (13, 103)]
    functions := []
    maxVar := 0
    target := .rv64i }

example :
      loopCompileProg primitiveLoopContext []
        (.primitive [10] .addCarry [11, 12, 13]) =
      .primitive [100] .addCarry [101, 102, 103] := by
  simp [loopCompileProg, lookupNatInfo, primitiveLoopContext]

example :
    loopCompileProg primitiveLoopContext []
        (.primitive [10] .addCarry [11, 99, 13]) = .skip := by
  simp [loopCompileProg, lookupNatInfo, primitiveLoopContext]

example :
    staticResultOk (staticCheck (α := Nat)
      [.decl .one "g" (.rStruct []), .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one }]) = false := by
  decide +kernel


end Flapjack
