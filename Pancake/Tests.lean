import Pancake.Language
import Pancake.Static
import Pancake.PanToCrep
import Pancake.Compile
import Pancake.Semantics
import Pancake.RiscV.Model

namespace Pancake

open RiscV

example : RiscV.Architecture.width .rv32i = 32 := by
  rfl

example : RiscV.accessAligned .read (0 : RiscV.Word 32) 4 = none := by
  native_decide

example : RiscV.writeRegister (RiscV.zeroState 32) 0 (7 : RiscV.Word 32) =
    RiscV.zeroState 32 := by
  simp [RiscV.writeRegister]

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

end Pancake
