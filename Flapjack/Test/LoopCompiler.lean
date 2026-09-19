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
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.globals.initializers.length = 1 ∧ result.crepe.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
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
#guard (reachedWarnable (.annot "" "" : Prog Nat) reachabilityContext).1.isNone
#guard (reachedWarnable (.tick : Prog Nat) reachabilityContext).1.isNone
#guard (reachedWarnable (.skip : Prog Nat)
  { reachabilityContext with reachable := .warnReach, last := .breakLast }).1 ==
    some .breakLast
#guard seqLastStmt .retLast .invisLast == .retLast
#guard staticLastStmtString .breakLast == "break"
#guard match basedMerge .based .notBased with | .based => true | _ => false
#guard match basedMerge .trusted .notBased with | .trusted => true | _ => false
#guard match shapedBasedMerge [.word .based, .word .notBased] with
  | .based => true | _ => false

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
