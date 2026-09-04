import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Pipeline
import Flapjack.Static
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.RiscV.Model
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.LoopSemantics
import Flapjack.Word
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Calls
import Flapjack.RiscV.Link
import Flapjack.Correctness
import Flapjack.WordSemantics

namespace Flapjack

open RiscV

example : RiscV.Architecture.width .rv32i = 32 := by
  rfl

example : RiscV.accessAligned .read (0 : RiscV.Word 32) 4 = none := by
  native_decide

example : RiscV.writeRegister (RiscV.zeroState 32) 0 (7 : RiscV.Word 32) =
    RiscV.zeroState 32 := by
  simp [RiscV.writeRegister]

example (state : RiscV.State 32) (source : Fin 32) (immediate : RiscV.Word 32) :
    (RiscV.execute state (.addi 0 source immediate)).pc = state.pc + 4 := by
  simp [RiscV.execute, RiscV.nextPc, RiscV.writeRegister]

def sampleShape : Shape := .comb [.one, .comb [.one, .one]]

example : Shape.shapeSize sampleShape = 3 := by
  simp [sampleShape, Shape.shapeSize]

example : nestedSeq ([] : List (Prog Nat)) = .skip := by
  rfl

example :
    expLocalVars (.op .add [.var .local "x", .var .global "g", .const 1]) = ["x"] := by
  native_decide

example :
    expGlobalVars (Exp.nStruct (α := Nat) "Pair"
      [("left", .var .local "x"), ("right", .var .global "g")]) = ["g"] := by
  native_decide

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

example : isWfShape pairContext (.named "Pair") = true := by
  native_decide

example : isWfShape pairContext (.comb [.one, .named "Pair"]) = true := by
  native_decide

example : isWfShape pairContext (.named "Missing") = false := by
  native_decide

example : isWfContext pairContext = true := by
  native_decide

example : shapeSizeWithContext pairContext (.named "Pair") = 2 := by
  native_decide

def duplicateContext : StructContext :=
  [("Pair", { fields := [], size := 0 }), ("Pair", { fields := [], size := 0 })]

example : isWfContext duplicateContext = false := by
  native_decide

example : validateDecl pairContext (.decl .one "answer" (.const 42)) = true := by
  native_decide

example : validateDecl pairContext (.decl (.named "Missing") "bad" (.const 0)) = false := by
  native_decide

def checkerContext : Context :=
  { locals := [("x", { shapedBased := .word .trusted }),
      ("pair", { shapedBased := .struct [.word .trusted, .word .trusted] })],
    globals := [("g", { shape := .one })], functions := [], exceptions := [],
    expectedReturn := none,
    structs := pairContext, scope := .topLevel, inLoop := false, reachable := .isReach,
    last := .otherLast, location := "" }

def checkerCallContext : Context :=
  { checkerContext with
    functions := [("f", { returnShape := .one, params := [] })] }

def checkerArgContext : Context :=
  { checkerContext with
    functions := [("f", { returnShape := .one, params := [("arg", .one)] })] }

def checkerPrimitiveContext : Context :=
  { checkerContext with
    locals := ("carry", { shapedBased := .struct [.word .notBased, .word .notBased] }) ::
      checkerContext.locals }

def checkerHandlerContext : Context :=
  { checkerCallContext with
    locals := ("exceptionValue", { shapedBased := .word .trusted }) ::
      checkerCallContext.locals,
    exceptions := [("E", .one)] }

example :
    checkExp (α := Nat) checkerContext (.var .local "x") =
      staticOk { shapedBased := .word .trusted } := by
  simp [checkExp, staticOk, checkerContext, pairContext, lookupInfo]

example :
    checkExp (α := Nat) checkerContext (Exp.rField 1 (Exp.var .local "pair")) =
      staticOk { shapedBased := .word .trusted } := by
  simp [checkExp, staticOk, staticBind, shapedBasedFieldAt,
    shapedBasedFieldAt.shapedBasedFieldAtList,
    checkerContext, pairContext, lookupInfo]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1, .const 2]) =
      staticOk { shapedBased := .word .notBased } := by
  simp [checkExp, checkExp.checkExps, staticOk, staticBind,
    shapedBasedIsWord, checkerContext, pairContext]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1]) =
      staticError (.general "invalid binary operator arity") := by
  simp [checkExp, checkExp.checkExps, staticOk, staticBind,
    checkerContext, pairContext]

example :
    checkProg (α := Nat) checkerContext (.return (.const 7)) =
      progOk .retLast true false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext]

example :
    checkProg (α := Nat) checkerContext
      (.assign .local "x" (.const 7)) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext, lookupInfo,
    shapedBasedSameShape]

example :
    checkProg (α := Nat) checkerContext
      (.assign .local "missing" (.const 7)) =
      staticError (.scope "unknown local variable: missing") := by
  simp [checkProg, staticError, staticBind, checkerContext, lookupInfo]

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext
      (.seq (.annot "location" "body")
        (.assign .local "missing" (.const 7)))) =
      some "unknown local variable: missing" := by
  native_decide

example :
    staticResultLocation (checkProg (α := Nat) checkerContext
      (.seq (.annot "location" "body") (.skip))) = some "AT body: " := by
  native_decide

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext
      (.ite (.const 1) (.annot "location" "then")
        (.assign .local "missing" (.const 7)))) =
      some "unknown local variable: missing" := by
  native_decide

example :
    checkProg (α := Nat) checkerContext
      (.break) =
      staticError (.general "break used outside a loop") := by
  simp [checkProg, staticError, checkerContext]

example :
    checkProg (α := Nat) checkerContext
      (.dec "y" .one (.const 7) (.return (.var .local "y"))) =
      progOk .retLast true false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, isWfShape,
    shapedBasedMatchesShape,
    shapedBasedFromShape, shapedBasedSameShape, checkerContext, pairContext,
    lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext (.call none "f" []) =
      progOk .tailLast true false "" := by
  simp [checkProg, checkProg.checkCallArgs,
    staticOk, staticBind,
    functionArgumentsMatch, checkerCallContext, checkerContext, lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext
      (.call (some (none, none)) "f" []) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkCallDestination,
    staticOk, staticBind,
    functionArgumentsMatch, checkerCallContext, checkerContext, lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext
      (.call (some (some (.local, "x"), none)) "f" []) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkCallDestination,
    staticOk, staticBind, functionArgumentsMatch, checkerCallContext, checkerContext,
    lookupInfo, shapedBasedMatchesShape, shapedBasedFromShape, shapedBasedSameShape]

example :
    checkProg (α := Nat) checkerCallContext (.call none "missing" []) =
      staticError (.scope "unknown function: missing") := by
  simp [checkProg, checkerCallContext, checkerContext, lookupInfo, staticError]

example :
    checkProg (α := Nat) checkerArgContext
      (.call none "f" [.const 1]) =
      progOk .tailLast true false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkExp, staticOk, staticBind,
    functionArgumentsMatch, shapedBasedMatchesShape, shapedBasedFromShape,
    shapedBasedSameShape, checkerArgContext, checkerContext, lookupInfo]

example :
    staticResultOk (checkProg (α := Nat) checkerPrimitiveContext
      (.primitive "carry" .addCarry [.const 1, .const 2, .const 0])) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerHandlerContext
      (.call (some (none, some ("E", "exceptionValue", .skip))) "f" [])) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerCallContext
      (.decCall "result" .one "f" [] .skip)) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerContext
      (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4))) =
      true := by
  native_decide

example :
    checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1), ("right", .const 2)]) =
      staticOk { shapedBased := (.named "Pair"
        [("left", .word .notBased), ("right", .word .notBased)]) } := by
  simp [checkExp, checkExp.checkNamedExps, staticOk, staticBind,
    shapedBasedFieldsMatch, shapedBasedFromShape, shapedBasedSameShape,
    checkerContext, pairContext, lookupInfo]

example :
    (checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1)])) =
      staticError (.shape "named struct fields do not match") := by
  simp [checkExp, checkExp.checkNamedExps, staticOk, staticBind,
    shapedBasedFieldsMatch, shapedBasedFromShape, shapedBasedSameShape,
    checkerContext, pairContext, lookupInfo]

def crepContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 1 }

def callContext : CompileContext Nat :=
  { crepContext with functions := [("f", ([], .one))], exceptions := [("E", 9)] }

def assignmentContext : CompileContext Nat :=
  { vars := [("x", (.one, [0]))], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

def loopContext : LoopContext Nat :=
  { vars := [], functions := [("f", (64, 0))], maxVar := 2,
    target := .rv64i }

def wordContext : WordContext :=
  { vars := [(3, 2), (4, 3)] }

def identityFunction : FunDecl Nat :=
  { name := "identity", inline := false, exported := false, params := [("x", .one)],
    body := .return (.var .local "x"), returnShape := .one }

def constantFunction : FunDecl Nat :=
  { name := "constant", inline := false, exported := false, params := [],
    body := .return (.const 7), returnShape := .one }

example :
    (compileFunDecl assignmentContext identityFunction).params = [0] := by
  simp [compileFunDecl, compileParamVars, identityFunction]

example :
    (compileFunDecl assignmentContext identityFunction).body =
      .return [.var 0] := by
  simp [compileFunDecl, compileParamVars, identityFunction, compileProg, compileExp,
    lookupInfo]

example :
    (compileToCrepe assignmentContext [.function constantFunction]).head?.map
        CompiledFunction.body =
      some (.return [.const 7]) := by
  simp [compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    functionInfos, constantFunction, compileProg, compileExp]

example :
    compileExp crepContext (Exp.var .local "pair") =
      ([.var 0, .var 1], .comb [.one, .one]) := by
  simp [compileExp, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.rField 1 (Exp.var .local "pair")) =
      ([.var 1], .one) := by
  simp [compileExp, compileField, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.const (α := Nat) 7) = ([.const 7], .one) := by
  simp [compileExp]

example :
    compileExp crepContext (Exp.bytesInWord : Exp Nat) = ([.const 1], .one) := by
  simp [compileExp, crepContext]

example :
    compileProg assignmentContext
      (.assign .local "x" (.var .local "x")) =
      .dec 1 (.var 0) (.seq (.assign 0 (.var 1)) .skip) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, crepNestedSeq,
    assignmentContext, lookupInfo, distinctLists, crepExpVars]

example :
    loadShape (0 : Nat) 4 2 (.var 3) =
      [.load (.var 3), .load (.op .add [.var 3, .const 4])] := by
  simp [loadShape]

example :
    cexpHeads ([ [.var 0], [.var 1] ] : List (List (CrepExp Nat))) =
      some [.var 0, .var 1] := by
  rfl

example : compileProg crepContext .skip = (.skip : CrepProg Nat) := by
  simp [compileProg]

example :
    compileProg crepContext (.return (.const (α := Nat) 7)) =
      .return [.const 7] := by
  simp [compileProg, compileExp]

example :
    compileProg crepContext (.seq .skip (.tick : Prog Nat)) =
      .seq .skip .tick := by
  simp [compileProg]

example :
    compileProg crepContext (.call none "f" [.const (α := Nat) 1]) =
      .call none "f" [.const 1] := by
  simp [compileProg, compileArgs, compileExp]

example :
    compileProg callContext (.call (some (none, none)) "f" []) =
      .call (some ([2], none)) "f" [] := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, callContext,
    crepContext, lookupInfo]

example :
    compileProg callContext
      (.call (some (none, some ("E", "missing", .skip))) "f" []) =
      .call (some ([2], some (9, .seq .skip .skip))) "f" [] := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, compileProg,
    callContext, crepContext, lookupInfo]

example :
    compileProg callContext (.raise "E" (.const (α := Nat) 0)) =
      .seq (.dec 2 (.const 0) (.seq (.storeGlob 0 (.var 2)) .skip)) (.raise 9) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, storeGlobals, crepNestedSeq,
    callContext, crepContext, lookupInfo]

example :
    compileProg assignmentContext
      (.primitive "x" .addCarry [.const (α := Nat) 3]) =
      .dec 1 (.const 3) (.primitive [0] .addCarry [1]) := by
  simp [compileProg, compileExp, compileArgs, freshNames, nestedDecs,
    assignmentContext, lookupInfo]

example :
    compileProg assignmentContext
      (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4)) =
      .dec 1 (.const 1)
        (.dec 2 (.const 2)
          (.dec 3 (.const 3)
            (.dec 4 (.const 4) (.extCall "ffi" 1 2 3 4)))) := by
  simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
    assignmentContext]

example :
    compileProg assignmentContext
      (.shMemLoad .op8 .local "x" (.const 10)) =
      .shMem .load8 0 (.const 10) := by
  simp [compileProg, firstCompiledExp, compileExp, loadMemOp,
    assignmentContext, lookupInfo]

example :
    compileProg assignmentContext
      (.shMemStore .op8 (.const 10) (.const 7)) =
      .dec 1 (.const 7) (.shMem .store8 1 (.const 10)) := by
  simp [compileProg, firstCompiledExp, compileExp, storeMemOp, nestedDecs,
    assignmentContext]

example :
    evalCrepProg (fun _ => none) (compileProg crepContext (.return (.const (α := Nat) 7))) =
      some [7] := by
  simp [compileProg, evalCrepProg, evalCrepExps, evalCrepExp, compileExp]

example :
    (evalCrepStateProg (fun _ => none)
        (compileProg assignmentContext
          (.seq (.assign .local "x" (.const 7))
            (.return (.var .local "x"))))).map Prod.snd =
      some [7] := by
  simp [compileProg, compileExp, crepNestedSeq, evalCrepStateProg, evalCrepExp, evalCrepExps,
    updateCrepLocal, assignmentContext,
    lookupInfo, distinctLists]

example :
    evalCrepMemResult (fun _ => none) (fun _ => none)
      (compileProg assignmentContext
        (.seq (.store (.const 10) (.const 7))
          (.return (.load .one (.const 10))))) =
      some [7] := by
    simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    loadShape, evalCrepMemResult, evalCrepMemProg, evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, updateMemory, updateCrepLocal, assignmentContext]

example :
    lowerLoopExp (CrepExp.cmp .equal (.var 0) (.const (α := Nat) 1)) =
      .cmp .equal (.var 0) (.const 1) := by
  simp [lowerLoopExp]

example :
    lowerLoopProg (CrepProg.seq .skip (.tick : CrepProg Nat)) =
      .seq .skip .tick := by
  simp [lowerLoopProg]

example :
    lowerLoopProg (CrepProg.store (.const (α := Nat) 0) (.const 7)) =
      (.fail : LoopProg Nat) := by
  simp [lowerLoopProg]

example :
    (loopCompileExp loopContext 3 [] (.load32 (.const (α := Nat) 8))).code =
      [.assign 3 (.const 8), .load32 3 3] := by
  simp [loopCompileExp]

example :
    loopCompileProg loopContext []
      (.return [(.const (α := Nat) 7)]) =
      .seq (.seq (.assign 3 (.const 7)) .skip) (.return [3]) := by
  simp [loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, loopContext]

example :
    loopCompileProg loopContext []
        (.store32 (.const (α := Nat) 8) (.const 255)) =
      .seq .skip
        (.seq (.assign 3 (.const 8))
          (.seq (.assign 4 (.const 255)) (.store32 3 4))) := by
  simp [loopCompileProg, loopCompileExp, loopCompileExps, loopNestedSeq,
    loopContext]

example :
    loopToWordExp (LoopExp.baseAddr : LoopExp Nat) = some (.lookup .currHeap) := by
  simp [loopToWordExp]

example :
    loopToWordProg wordContext (.assign 3 (.const (α := Nat) 7)) =
      .assign 2 (.const 7) := by
  simp [loopToWordProg, wordCompileExp, wordFindVar, lookupNatInfo, wordContext]

example :
    loopToWordProg wordContext (.seq (.load32 3 4) (.store32 3 4)) =
      .seq (.inst (.mem .load32 3 2)) (.inst (.mem .store32 3 2)) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo, wordContext]

example :
    loopVarsOfExp ((LoopExp.op .add [.var 1, .load (.var 2)]) : LoopExp Nat) =
      [1, 2] := by
  simp [loopVarsOfExp]

example :
    loopAssignedVars (LoopProg.seq (.assign 1 (.const 0)) (.load32 1 2)) = [1, 2] := by
  rfl

example :
    loopAccVars (LoopProg.assign 1 (.op .add [.var 2, .const 0])) [] = [2, 1] := by
  native_decide

example [NeZero width] :
    Flapjack.RiscV.compileWordAdd (width := width) 1 2 3 =
      some [.add 1 2 3] := by
  simp [Flapjack.RiscV.compileWordAdd, Flapjack.RiscV.wordProgToRiscV,
    Flapjack.RiscV.wordExpToInstruction, Flapjack.RiscV.registerOfNat]

example [NeZero width] (state : Flapjack.RiscV.State width)
    (zero : Flapjack.RiscV.readRegister state 0 = 0) :
    Flapjack.RiscV.evalWordProg state
        (.assign 1 (.const (7 : Flapjack.RiscV.Word width))) =
      some (Flapjack.RiscV.execute state (.addi 1 0 7)) := by
  simp [Flapjack.RiscV.evalWordProg, Flapjack.RiscV.wordExpToInstructions,
    Flapjack.RiscV.wordExpToInstruction, Flapjack.RiscV.evalWordExp,
    Flapjack.RiscV.registerOfNat, Flapjack.RiscV.executeInstructions,
    Flapjack.RiscV.execute,
    Flapjack.RiscV.writeRegister, Flapjack.RiscV.nextPc, zero]

example [NeZero width] :
    Flapjack.RiscV.ZeroRegister (Flapjack.RiscV.zeroState width) := by
  exact Flapjack.RiscV.zeroState_zeroRegister

example [NeZero width] (state : Flapjack.RiscV.State width)
    (operator : BinOp) :
    Flapjack.RiscV.evalWordProg state
        (.assign 1 (.op operator [.var 2, .var 3])) =
      some (Flapjack.RiscV.execute state (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3)) := by
  exact Flapjack.RiscV.compileWordBinOp_sound state operator

example [NeZero width] :
    Flapjack.RiscV.wordFunctionToRiscV
        ((.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) :
          WordProg (Flapjack.RiscV.Word width)) =
      some ([.add 1 2 3], [1]) := by
  exact Flapjack.RiscV.wordFunctionToRiscV_return_add

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notEqual 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchEq 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notEqual 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchEq 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .equal 1 (.imm 7)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) =
      some [.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2] := by
  native_decide

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .test 1 (.imm 3)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) =
      some [.andi 31 1 3, .branchNe 31 0 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2] := by
  native_decide

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .equal 31 (.imm 7)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) = none := by
  native_decide

example :
    RiscV.wordFunctionToRiscV (width := 8)
        ((.seq
          (.ite .equal 1 (.imm 7)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word 8)) =
      some ([.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2], [3]) := by
  native_decide

example :
    (RiscV.executeCode 20 (0 : RiscV.Word 8)
      [.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2]
      (RiscV.writeRegister (RiscV.zeroState 8) 1 7)).map
        (fun state => RiscV.readRegister state 3) = some 1 := by
  native_decide

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .lower 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGeU 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLower 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLtU 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .test 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.and 1 1 2, .branchNe 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notTest 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.and 1 1 0, .branchEq 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .less 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLess 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLt 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .less 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLess 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLt 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq
          (.ite .equal 1 (.reg 2)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2], [3]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordProgToRiscV,
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq (.return 0 [1]) (.assign 2 (.const 9))) :
          WordProg (RiscV.Word width)) =
      some ([], [1]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordFunction state
        ((.seq (.return 0 [1]) (.assign 2 (.const 9))) :
          WordProg (RiscV.Word width)) =
      some (state, [RiscV.readRegister state 1]) := by
  simp [RiscV.evalWordFunction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.seq (.assign 3 (.const 1)) (.return 0 [3]))
          (.seq (.assign 3 (.const 2)) (.return 0 [3]))) :
          WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8),
        .addi 3 0 2], [3]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordProgToRiscV,
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq
          (.ite .equal 1 (.reg 2)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.seq .tick (.return 0 [3]))) : WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8),
        .addi 3 0 2, .addi 0 0 0], [3]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordProgToRiscV,
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    (RiscV.executeCode 10 (0 : RiscV.Word 32)
      [.branchNe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (RiscV.zeroState 32)).map (fun state => RiscV.readRegister state 3) =
      some 1 := by
  native_decide

example :
    (RiscV.executeCode 10 (0 : RiscV.Word 32)
      [.branchEq 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (RiscV.zeroState 32)).map
        (fun state => RiscV.readRegister state 3) =
      some 2 := by
  native_decide

example :
    panSimpProg (.seq (.skip : Prog Nat) (.return (.const 7))) =
      .return (.const 7) := by
  simp [panSimpProg, seqAssoc, retToTail, smartSeq]

example :
    panSimpProg
        ((.seq
          (.call (some (some (.local, "result"), none)) "f" [])
          (.return (.var .local "result"))) : Prog Nat) =
      (.call none "f" [] : Prog Nat) := by
  simp [panSimpProg, seqAssoc, retToTail, seqCallRet, smartSeq]

example :
    structCompileShape
        [("pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
        (.named "pair") = .comb [.one, .one] := by
  simp [structCompileShape, structCompileShapeFuel, lookupInfo]

example :
    structCompileExp
        { structs := [("pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
          locals := [("p", .named "pair")]
          globals := [] }
        (.nField "right" (.nStruct "pair" [("right", .const 7), ("left", .const 3)])) =
      .rField 1 (.rStruct [.const 3, .const 7]) := by
  simp [structCompileExp, structCompileExp.structCompileFields,
    structCompileExp.structCompileExps, structOldExpShape, structFindFieldIndex,
    structSelectFields, lookupInfo]

def globalTestContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

example :
    globalCompileExp globalTestContext (.var .global "g") =
      .load .one (.op .sub [.topAddr, .const 8]) := by
  simp [globalCompileExp, globalTestContext, lookupInfo]

example :
    globalCompileProg globalTestContext
        (.assign .global "g" (.const 7)) =
      .store (.op .sub [.topAddr, .const 8]) (.const 7) := by
  simp [globalCompileProg, globalCompileExp, globalTestContext, lookupInfo]

example :
    let result := globalCompileTop (α := Nat) 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.context.globalsSize = 1 := by
  simp [globalCompileTop, globalCollect, globalAddress, globalCompileDecls,
    globalCompileInitializers, globalCompileProg, globalCompileExp, lookupInfo]

example :
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.const 7), returnShape := .one }]
    result.simplified.length = 1 ∧ result.structured.length = 1 ∧
      result.crepe.length = 1 ∧ result.loop.length = 1 ∧ result.word.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineExceptionCodes,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers,
    compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    compileProg, loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq, loopTempNames, wordFindVar, lookupInfo,
    lookupNatInfo]

example [NeZero width] :
    pipelineRiscVFunctions
        (width := width)
        [(0, [], ((.seq (.assign 1 (.op .add [.var 2, .var 3]))
          (.return 0 [1])) : WordProg (RiscV.Word width)))] =
      [(0, [], some ([.add 1 2 3], [1]))] := by
  simp [pipelineRiscVFunctions, RiscV.wordFunctionToRiscVWithLoops,
    RiscV.wordFunctionToRiscVWithLoopsAux, RiscV.wordControlInstructions,
    RiscV.wordFunctionToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] (state : RiscV.State width) (value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state) :
    RiscV.evalWordFunction state
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (RiscV.Word width)) =
      some (RiscV.execute state (.addi 1 0 value),
        [RiscV.readRegister (RiscV.execute state (.addi 1 0 value)) 1]) := by
  exact RiscV.evalWordFunction_return_const state value zero

def loopProgLongMulFingerprint : LoopProg α → Option (Nat × Nat × Nat × Nat)
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      some (destinationLeft, destinationRight, sourceLeft, sourceRight)
  | _ => none

example :
    (loopCompileExp loopContext 3 []
      (.crepOp .mul [.var 0, .var 1])).code.map loopProgLongMulFingerprint =
      [none, none, some (5, 5, 3, 4)] := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.panOp .mul [.const (BitVec.ofNat 64 2),
            .const (BitVec.ofNat 64 3)]), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      pipelineAddDeclarations
    result.linkedFunctions.isSome := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      pipelineAddDeclarations
    result.callLinkedFunctions.isSome := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "add", inline := false, exported := false,
          params := [("left", .one), ("right", .one)],
          body := .return (.op .add
            [.var .local "left", .var .local "right"]), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, parameters, artifact) =>
        parameters = [2, 3] && match artifact with
        | some (code, returns) =>
            returns = [5] && match code with
            | [.add destination left right] =>
                destination = 5 && left = 2 && right = 3
            | _ => false
        | none => false) := by
  native_decide

example : compiledPipelineAddRun 7 8 = some [15] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.add 5 2 3] [5] [7, 8] (RiscV.zeroState 64) = some [15] := by
  exact RiscV.executeFunction_add

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.divU 5 2 3] [5] [42, 6] (RiscV.zeroState 64) = some [7] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.remU 5 2 3] [5] [43, 6] (RiscV.zeroState 64) = some [1] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.divU 5 2 3] [5] [42, 0] (RiscV.zeroState 64) =
        some [BitVec.ofNat 64 (2 ^ 64 - 1)] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.remU 5 2 3] [5] [42, 0] (RiscV.zeroState 64) = some [42] := by
  native_decide

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.addCarry 5 6 2 3 4) =
      some [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] := by
  exact RiscV.wordArithToInstructions_addCarry

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.op .and [.var 2, .const (15 : RiscV.Word width)]) =
      some (.andi 1 2 15) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.op .sub [.var 2, .const (4 : RiscV.Word width)]) =
      some (.addi 1 2 (0 - 4)) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.shift .lsr (.var 2) (.const (3 : RiscV.Word width))) =
      some (.srli 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 8) [2]
      [.andi 5 2 15, .ori 6 5 16, .xori 7 6 3] [7] [BitVec.ofNat 8 10]
      (RiscV.zeroState 8) = some [25] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 8) [2]
      [.slli 5 2 2, .srli 6 5 1, .srai 7 6 1] [7] [BitVec.ofNat 8 10]
      (RiscV.zeroState 8) = some [10] := by
  native_decide

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.longMul 1 2 3 4) =
      some [.mulHU 1 3 4, .mul 2 3 4] := by
  exact RiscV.wordArithToInstructions_longMul

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.longMul 3 2 3 4) = none := by
  exact RiscV.wordArithToInstructions_longMul_alias

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.addCarry 31 6 2 3 4) = none := by
  simp [RiscV.wordArithToInstructions]

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3, 4]
      [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] [5, 6]
      [BitVec.ofNat 8 255, 1, 1] (RiscV.zeroState 8) = some [1, 1] := by
  native_decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3]
      [.mulHU 5 2 3, .mul 6 2 3] [5, 6]
      [BitVec.ofNat 8 255, 2] (RiscV.zeroState 8) = some [1, 254] := by
  native_decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3, 4]
      [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] [5, 6] [10, 20, 7]
      (RiscV.zeroState 8) = some [31, 0] := by
  native_decide

example :
    loopToWordProg ({ vars := [] } : WordContext)
      (.primitive [7, 8] .addCarry [2, 3, 4]) =
      .seq (.assign 1 (.var 4))
        (.seq (.inst (.arith (.addCarry 3 1 2 3 1)))
          (.seq (.assign 8 (.var 1)) (.assign 7 (.var 3)))) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo]

example [NeZero width] :
    RiscV.wordArithToInstruction (width := width) (.div 1 2 3) =
      some (.divU 1 2 3) := by
  exact RiscV.wordArithToInstruction_div

example (left right : RiscV.Word 64) :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.add 5 2 3] [5] [left, right] (RiscV.zeroState 64) = some [left + right] := by
  exact RiscV.executeFunction_add_general left right

def linkedCallCode : List (RiscV.Instruction 64) :=
  [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0,
    .addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
    .addi 10 2 1, .jalr 0 1 0]

example :
    RiscV.wordCallToRiscV (32 : RiscV.Word 64) [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0] := by
  exact RiscV.wordCallToRiscV_shape 32

example :
    (RiscV.executeCodeUntil 30 (0 : RiscV.Word 64) 16 linkedCallCode
      (RiscV.writeRegister (RiscV.zeroState 64) 6 41)).map
        (fun state => RiscV.readRegister state 4) = some 42 := by
  native_decide

example :
    RiscV.linkRiscVFunctions (0 : RiscV.Word 64)
      [(7, [2], some ([.addi 10 2 1, .jalr 0 1 0], [10]))] =
      some [(7, 0, [2], [.addi 10 2 1, .jalr 0 1 0], [10])] := by
  rfl

example :
    RiscV.wordCallToRiscVLabel
      [(7, (32 : RiscV.Word 64), [2], [], [10])] 7 [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0] := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.seq
        (.call (some ([4], [])) (some 7) [6] none)
        (.return 0 [4])) =
      some ([.addi 2 6 0, .addi 30 30 (0 - BitVec.ofNat width (width / 8)),
        .storeWord 1 30, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 1 31 0, .addi 4 10 0, .loadWord 1 30,
        .addi 30 30 (BitVec.ofNat width (width / 8))], [4]) := by
  exact RiscV.wordFunctionToRiscVWithCalls_shape

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.shareInst .load 1 (.var 2)) : WordProg (RiscV.Word width)) =
      some ([.loadWord 1 2], []) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load32 5 (.var 6)) : WordProg (RiscV.Word width)) =
      some ([.load32 5 6], []) := by
  exact RiscV.wordFunctionToRiscVWithCalls_shareInst

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load16 5 (.var 6)) : WordProg (RiscV.Word width)) =
      some ([.loadHalf 5 6], []) := by
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.registerOfNat]

def halfwordRoundTripState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister (RiscV.zeroState 64) 2 16) 3
      (BitVec.ofNat 64 0xBEEF)

example :
    (RiscV.evalWordFunction halfwordRoundTripState
      (.seq (.inst (.mem .store16 3 2)) (.inst (.mem .load16 1 2)))).map
        (fun result => RiscV.readRegister result.1 1) =
      some (BitVec.ofNat 64 0xBEEF) := by
  native_decide

example :
    RiscV.wordFunctionToRiscVWithCalls (width := 8)
        ({ targets := [] } : RiscV.WordCallContext 8)
        ((.seq
          (.ite .equal 1 (.imm 7)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word 8)) =
      some ([.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2], [3]) := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load32 5
          (.op .add [.var 6, .const (4 : RiscV.Word width)])) :
          WordProg (RiscV.Word width)) =
      some ([.addi 31 6 4, .load32 5 31], []) := by
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordShareInstToInstructions, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.wordInstToInstruction,
    RiscV.registerOfNat]

def selectedLinkedCallCode : List (RiscV.Instruction 64) :=
  match RiscV.wordFunctionToRiscVWithCalls
      { targets := [(7, (32 : RiscV.Word 64), [2], [10])] }
      (.seq
        (.call (some ([4], [])) (some 7) [6] none)
        (.return 0 [4])) with
  | some (code, _) => code ++
      [.addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
        .addi 10 2 1, .jalr 0 1 0]
  | none => []

example :
    (RiscV.executeCodeUntil 40 (0 : RiscV.Word 64) 24 selectedLinkedCallCode
      (RiscV.writeRegister (RiscV.zeroState 64) 6 41)).map
        (fun state => RiscV.readRegister state 4) = some 42 := by
  native_decide

def linkedWordCallFunctions :
    List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
  [(7, [2], .return 0 [2]),
   (8, [6], .seq
      (.call (some ([4], [])) (some 7) [6] none)
      (.return 0 [4]))]

example :
    RiscV.linkWordFunctions (0 : RiscV.Word 64) linkedWordCallFunctions =
      some [
        (7, 0, [2], [.jalr 0 1 0], [2]),
        (8, 4, [6],
          [.addi 2 6 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
            .storeWord 1 30, .addi 31 0 0, .jalr 1 31 0,
            .addi 4 2 0, .loadWord 1 30, .addi 30 30 (BitVec.ofNat 64 8),
            .jalr 0 1 0], [4])] := by
  simp [RiscV.linkWordFunctions, RiscV.wordFunctionTargetSignatures,
    RiscV.wordFunctionTargetSignaturesWithCalls,
    RiscV.wordFunctionTargetSignaturesAux,
    RiscV.wordFunctionReturnNamesWithCalls, RiscV.lookupWordFunctionBody,
    RiscV.compileLinkedWordFunction, RiscV.wordFunctionReturnNames,
    RiscV.wordFunctionToRiscVWithCallsAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndLoopsAux,
    RiscV.wordControlInstructions, RiscV.resolveWordLoopBody,
    RiscV.resolveWordLoopBodyAux,
    RiscV.wordFunctionToRiscVWithCalls, RiscV.wordCallToRiscVWithStack,
    RiscV.wordCallToRiscV,
    RiscV.wordRegisterMoves, RiscV.lookupWordCallTarget,
    RiscV.registerOfNat, RiscV.linkRiscVFunctions,
    RiscV.linkRiscVFunctionsAt, linkedWordCallFunctions]

def linkedWordLoopFunctions :
    List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
  [(7, [], (.loop [] (.break 0) []))]

example :
    RiscV.linkWordFunctions (0 : RiscV.Word 64) linkedWordLoopFunctions =
      some [(7, 0, [],
        [.jal 0 (BitVec.ofNat 64 8),
         .jal 0 (0 - BitVec.ofNat 64 4), .jalr 0 1 0], [])] := by
  simp [RiscV.linkWordFunctions, RiscV.wordFunctionTargetSignatures,
    RiscV.wordFunctionTargetSignaturesWithCalls,
    RiscV.wordFunctionTargetSignaturesAux,
    RiscV.wordFunctionReturnNamesWithCalls, RiscV.lookupWordFunctionBody,
    RiscV.compileLinkedWordFunction, RiscV.wordFunctionReturnNames,
    RiscV.wordFunctionToRiscVWithCallsAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndLoopsAux,
    RiscV.wordControlInstructions, RiscV.resolveWordLoopBody,
    RiscV.resolveWordLoopBodyAux, RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordCallToRiscVWithStack, RiscV.wordCallToRiscV,
    RiscV.wordRegisterMoves, RiscV.lookupWordCallTarget,
    RiscV.registerOfNat, RiscV.linkRiscVFunctions,
    RiscV.linkRiscVFunctionsAt, linkedWordLoopFunctions]

def linkedWordCallImage : List (RiscV.Instruction 64) :=
  [.jalr 0 1 0, .addi 2 6 0,
    .addi 30 30 (0 - BitVec.ofNat 64 8), .storeWord 1 30,
    .addi 31 0 0, .jalr 1 31 0, .addi 4 2 0,
    .loadWord 1 30, .addi 30 30 (BitVec.ofNat 64 8), .jalr 0 1 0]

example :
    RiscV.executeFunctionAt 80 (0 : RiscV.Word 64) 4 36 [6]
      linkedWordCallImage [4] [41] (RiscV.zeroState 64) = some [41] := by
  native_decide

example :
    (RiscV.evalWordFunctionWithCalls
      [(7, [2], (.return 0 [2] : WordProg (RiscV.Word 64)))] 10
      (RiscV.writeRegister (RiscV.zeroState 64) 2 9)
      (.call (some ([3], [])) (some 7) [2] none)).map (fun result =>
        result.1.registers 3) = some 9 := by
  native_decide

example :
    (RiscV.evalWordFunctionWithHandlers
      [(7, [2], (.seq (.assign 4 (.const (9 : RiscV.Word 64)))
        (.raise 4) : WordProg (RiscV.Word 64)))] 10
      (RiscV.zeroState 64)
      (.call (some ([3], [])) (some 7) [2]
        (some (5, (.return 0 [5] : WordProg (RiscV.Word 64)))))).map
        (fun result =>
          match result with
          | .returned state values => (RiscV.readRegister state 5, values)
          | _ => (0, [])) = some (9, [9]) := by
  native_decide

def wordFfiTestState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister
      (RiscV.writeRegister
        (RiscV.writeRegister (RiscV.zeroState 64) 1 10) 2 1) 3 20) 4 2

def wordFfiTestHandler : FunName → RiscV.Word 64 → RiscV.Word 64 →
    RiscV.Word 64 → RiscV.Word 64 → RiscV.State 64 →
    Option (RiscV.State 64) := fun function configuration configurationLength array
    arrayLength state =>
  if function == "sum" then
    some (RiscV.writeRegister state 5
      (configuration + configurationLength + array + arrayLength))
  else none

example :
    (RiscV.evalWordFfi wordFfiTestHandler 10 wordFfiTestState
      (.ffi "sum" 1 2 3 4 [])).map (fun result =>
        RiscV.readRegister result.1 5) = some 33 := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq (.assign 1 (.const (BitVec.ofNat width 100)))
          (.seq (.assign 2 (.const (BitVec.ofNat width 42)))
            (.seq (.store (.var 1) 2) (.seq (.inst (.mem .load 3 1))
              (.return 0 [3]))))) : WordProg (RiscV.Word width)) =
      some ([.addi 1 0 (BitVec.ofNat width 100),
        .addi 2 0 (BitVec.ofNat width 42), .storeWord 2 1, .loadWord 3 1], [3]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordStoreToInstructions,
    RiscV.wordShareInstToInstructions, RiscV.wordExpToInstruction,
    RiscV.wordInstToInstruction, RiscV.registerOfNat]

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 64) []
      [.addi 1 0 100, .addi 2 0 42, .storeWord 2 1, .loadWord 3 1]
      [3] [] (RiscV.zeroState 64) = some [42] := by
  exact RiscV.executeFunction_storeLoad

example [NeZero width] (state : RiscV.State width)
    (offset : RiscV.Word width) :
    (RiscV.execute state (.jal 1 offset)).pc = state.pc + offset := by
  exact RiscV.execute_jal_pc state 1 offset

example [NeZero width] (state : RiscV.State width) (source : Fin 32)
    (offset : RiscV.Word width) :
    (RiscV.execute state (.jalr 1 source offset)).pc =
      RiscV.jalrTarget (RiscV.readRegister state source) offset := by
  exact RiscV.execute_jalr_pc state 1 source offset

example :
    (RiscV.execute
      (RiscV.writeRegister (RiscV.zeroState 64) 2 (100 : RiscV.Word 64))
      (.jalr 1 2 3)).pc = 102 := by
  native_decide

example :
    RiscV.executeFunctionAt 20 (0 : RiscV.Word 64) 16 4 []
      [.addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
        .addi 10 0 42, .jalr 0 1 0] [10] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 4) = some [42] := by
  exact RiscV.executeFunctionAt_jalr_return

def loopCallTestState : LoopState Nat :=
  { locals := fun name => if name = 1 then some 9 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopSharedMemoryTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 100 else if name = 2 then some 42 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 10 else if name = 2 then some 1
      else if name = 3 then some 20 else if name = 4 then some 2 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestHandler : FunName → Nat → Nat → Nat → Nat → LoopState Nat →
    Option (LoopState Nat) := fun function configuration configurationLength array arrayLength state =>
  if function == "sum" then
    let value := configuration + configurationLength + array + arrayLength
    some { state with locals := updateLoopLocal state.locals 5 value }
  else none

example :
    (evalLoopProg 10 loopSharedMemoryTestState
      (.seq
        (.shMem .store 2 (.var 1))
        (.shMem .load 3 (.var 1)))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 42) := by
  native_decide

example :
    (evalLoopFfi loopFfiTestHandler 10 loopFfiTestState
      (.ffi "sum" 1 2 3 4 [])).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  native_decide

example :
    (evalLoopProgWithCallsAndFfi
      [(7, [1], (.return [1] : LoopProg Nat))]
      loopFfiTestHandler 20 loopFfiTestState
      (.seq
        (.call (some ([6], [])) (some 7) [1] none)
        (.ffi "sum" 1 2 3 4 []))).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(7, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 7) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(8, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call none (some 8) [1] none)).map loopResultValues = some [9] := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(9, [1], (.raise 1 : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 9) [1]
        (some (4, .assign 3 (.var 4), .skip, [])))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(10, [1],
          (.seq
            (.call (some ([2], [])) (some 11) [1] none)
            (.return [2]) : LoopProg Nat)),
       (11, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 10) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(12, [1], (.return [1] : LoopProg Nat))] 20 loopCallTestState
      (.loop []
        (.seq
          (.call (some ([3], [])) (some 12) [1] none)
          (.break 0)) [])).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .ite (.cmp .equal (.const (BitVec.ofNat 64 1))
            (.const (BitVec.ofNat 64 1)))
            (.return (.const (BitVec.ofNat 64 7)))
            (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  native_decide

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  native_decide

example :
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.globals.initializers.length = 1 ∧ result.crepe.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineExceptionCodes,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers,
    compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    compileProg, loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq, loopTempNames, wordFindVar, lookupInfo,
    lookupNatInfo]

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.rStruct []), returnShape := .one }]) = false := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  native_decide

example :
    (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .seq (.return (.const 7)) .skip, returnShape := .one }]).2.length = 1 := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one },
       .function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 1), returnShape := .one }]) = false := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.decl .one "g" (.rStruct []), .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one }]) = false := by
  native_decide

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsl (.var 2) (.var 3)) =
      some (.sll 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsr (.var 2) (.var 3)) =
      some (.srl 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .asr (.var 2) (.var 3)) =
      some (.sra 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .ror (.var 2) (.var 3)) = none := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) =
      some [.srli 31 2 3, .slli 1 2 5, .or 1 1 31] := by
  native_decide

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.var 3)) =
      some [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] := by
  native_decide

example :
    RiscV.wordExpToInstructions (width := 8) 31
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) = none := by
  native_decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2]
      [.srli 31 2 1, .slli 1 2 7, .or 1 1 31] [1]
      [129] (RiscV.zeroState 8) = some [192] := by
  native_decide

example :
    RiscV.executeFunction 30 (0 : RiscV.Word 8) [2, 3]
      [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] [1]
      [129, 1] (RiscV.zeroState 8) = some [192] := by
  native_decide

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.var 3))) =
      some (RiscV.execute state (.sll 1 2 3)) := by
  exact RiscV.compileWordShiftLsl_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.var 3))) =
      some (RiscV.execute state (.srl 1 2 3)) := by
  exact RiscV.compileWordShiftLsr_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.var 3))) =
      some (RiscV.execute state (.sra 1 2 3)) := by
  exact RiscV.compileWordShiftAsr_sound state

example :
    RiscV.shiftAmount (BitVec.ofNat 64 65) = 1 := by
  native_decide

example :
    evalPanExp (fun _ => none)
      (.panOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  native_decide

example :
    evalCrepExp (fun _ => none)
      (.crepOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  native_decide

example :
    evalCrepProg (fun _ => none)
        (compileProg crepContext
          (.return (.panOp .mul [.const (α := Nat) 6, .const 7]))) =
      evalPanProg (fun _ => none)
        (.return (.panOp .mul [.const (α := Nat) 6, .const 7])) := by
  exact compile_pan_mul_const_preserves_semantics crepContext 6 7
    (fun _ => none) (fun _ => none)

def emptyLoopState : LoopState Nat :=
  { locals := fun _ => none, globals := fun _ => none, memory := fun _ => none }

def loopDivisionState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 42 else if name = 2 then some 6 else none
    globals := fun _ => none, memory := fun _ => none }

example :
    (evalLoopProg 10 loopDivisionState
      (.seq (.arith (.div 3 1 2)) (.return [3]))).map loopResultValues =
      some [7] := by
  native_decide

example :
    (evalLoopProg 1 loopDivisionState (.arith (.div 3 1 2))).map
      (fun result => match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 7) := by
  native_decide

example :
    (evalLoopProg 1
      { loopDivisionState with locals := fun name =>
          if name = 1 then some 42 else if name = 2 then some 0 else none }
      (.arith (.div 3 1 2))).isNone = true := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .add [.const 6, .crepOp .mul [.const 5, .const 6]]) = some 36 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .sub [.const 9, .const 4]) = some 5 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .and [.const 13, .const 6]) = some 4 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .or [.const 8, .const 3]) = some 11 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .xor [.const 13, .const 6]) = some 11 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsl (.const 3) (.const 2)) = some 12 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsr (.const 13) (.const 2)) = some 3 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.cmp .lower (.const 3) (.const 5)) = some 1 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.cmp .notLower (.const 5) (.const 3)) = some 1 := by
  native_decide

example : evalLoopCondition .less (3 : Nat) 5 = some true := by
  native_decide

example : evalLoopCondition .notLess (5 : Nat) 3 = some true := by
  native_decide

example : evalLoopCondition .test (5 : Nat) 2 = some true := by
  native_decide

example : evalLoopCondition .notTest (5 : Nat) 1 = some true := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .less (.const (3 : Nat)) (.const 5)) =
    some 1 := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .test (.const (5 : Nat)) (.const 2)) =
    some 1 := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .notTest (.const (5 : Nat)) (.const 1)) =
    some 1 := by
  native_decide

example :
    (evalLoopProg 10 emptyLoopState
      (.seq (.assign 0 (.const 42)) (.return [0]))).map loopResultValues =
      some [42] := by
  native_decide

example :
    evalLoopProg 1 emptyLoopState (.break 7) =
      some (.broke emptyLoopState 7) := by
  exact evalLoopProg_break emptyLoopState 7

example :
    evalLoopProg 1 emptyLoopState (.continue 8) =
      some (.continued emptyLoopState 8) := by
  exact evalLoopProg_continue emptyLoopState 8

example :
    evalLoopProg 1 emptyLoopState (.tick) =
      some (.normal emptyLoopState) := by
  exact evalLoopProg_tick emptyLoopState

example :
    (evalLoopProg 10 emptyLoopState
      (.loop [] (.break 0) [])).map loopResultValues = some [] := by
  native_decide

example :
    (evalLoopProg 12 emptyLoopState
      (loopCompileProg loopContext [] (.return [(.const (α := Nat) 7)]))).map
        loopResultValues = some [7] := by
  exact evalLoopCompile_return_const loopContext [] emptyLoopState 7

example :
    Option.map loopResultValues
      (evalLoopProg 20 emptyLoopState
      (loopCompileProg loopContext []
          (.return [(.crepOp .mul [.const (α := Nat) 6, .const 7])]))) =
      some [42] := by
  native_decide

example :
    evalPanCondition (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.cmp .equal (.var .local "x") (.const 7)) = some true := by
  native_decide

example :
    evalPanProg (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.ite (.cmp .equal (.var .local "x") (.const 7))
          (.return (.const 1)) (.return (.const 0))) = some [1] := by
  native_decide

example :
    (evalPanMemProgFuel 4
      (fun _ => none)
      (fun address => if address == 4 then some 7 else none)
      (.ite (.cmp .equal (.load .one (.const 4)) (.const 7))
        (.return (.const 1)) (.return (.const 0)))).map
      (fun result => result.2.2) = some [1] := by
  native_decide

end Flapjack
