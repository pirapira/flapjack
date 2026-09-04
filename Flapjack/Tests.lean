import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Static
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.RiscV.Model
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.Word
import Flapjack.RiscV.Backend

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
  simp [checkProg, staticError, checkerContext, lookupInfo]

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
    lookupInfo]

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
  simp [Flapjack.RiscV.evalWordProg, Flapjack.RiscV.evalWordExp,
    Flapjack.RiscV.registerOfNat, Flapjack.RiscV.execute,
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

end Flapjack
