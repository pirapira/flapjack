import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Pipeline
import Flapjack.Static
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.PanValues
import Flapjack.PanMemory
import Flapjack.RiscV.Model
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.LoopSemantics
import Flapjack.Word
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Calls
import Flapjack.RiscV.Link
import Flapjack.WordSemantics

namespace Flapjack

open RiscV

example : RiscV.Architecture.width .rv32i = 32 := by
  decide +kernel

example : RiscV.accessAligned .read (0 : RiscV.Word 32) 4 = none := by
  decide

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
  decide +kernel

example :
    expGlobalVars (Exp.nStruct (α := Nat) "Pair"
      [("left", .var .local "x"), ("right", .var .global "g")]) = ["g"] := by
  decide +kernel

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

example : isWfShape pairContext (.named "Pair") = true := by
  decide +kernel

example : isWfShape pairContext (.comb [.one, .named "Pair"]) = true := by
  decide +kernel

example : isWfShape pairContext (.named "Missing") = false := by
  decide +kernel

example : isWfContext pairContext = true := by
  decide +kernel

#guard shapeSizeWithContext pairContext (.named "Pair") = 2

def duplicateContext : StructContext :=
  [("Pair", { fields := [], size := 0 }), ("Pair", { fields := [], size := 0 })]

example : isWfContext duplicateContext = false := by
  decide

example : validateDecl pairContext (.decl .one "answer" (.const 42)) = true := by
  decide +kernel

example : validateDecl pairContext (.decl (.named "Missing") "bad" (.const 0)) = false := by
  decide +kernel

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

def checkerFunctionContext : Context :=
  { checkerCallContext with
    expectedReturn := some .one
    scope := .funScope "f" "" }

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
  simp [checkExp, staticOk, staticBind, checkerContext, pairContext, lookupInfo,
    checkLocalVar]

example :
    checkExp (α := Nat) checkerContext (Exp.rField 1 (Exp.var .local "pair")) =
      staticOk { shapedBased := .word .trusted } := by
  simp [checkExp, staticOk, staticBind, shapedBasedFieldAt,
    shapedBasedFieldAt.shapedBasedFieldAtList,
    checkerContext, pairContext, lookupInfo, checkLocalVar]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1, .const 2]) =
      staticOk { shapedBased := .word .notBased } := by
  simp [checkExp, checkExp.checkExps, checkOperands, staticOk, staticBind,
    basedMerge, checkerContext, pairContext]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1]) =
      staticError (.general (getOpargMessage false "2" (toString 1) ""
        (binopToString .add)
        .topLevel)) := by
  simp [checkExp, checkerContext, pairContext]

#guard
  staticResultErrorMessage
      (checkExp (α := Nat) checkerContext (Exp.op .add [.const 1])) ==
    some "operation Add requires at least 2 operands, 1 provided in top-level declaration\n"

#guard
  staticResultErrorMessage (checkProg (α := Nat) checkerContext
    (.return (.const 7))) ==
    some "return found outside function scope in top-level declaration\nthis should never happen. please report to a compiler developer\n"

example :
    checkProg (α := Nat) checkerContext (.return (.const 7)) =
      staticError (.general (getImplementationErrorMessage
        "return found outside function scope" "" .topLevel)) := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext]

example :
    checkProg (α := Nat) checkerContext
      (.assign .local "x" (.const 7)) =
      staticOk
        { exitsFunction := false, exitsLoop := false, last := .otherLast,
          variableDelta := [("x", { shapedBased := .word .notBased })],
          currentLocation := "" } := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext, lookupInfo,
    checkLocalVar,
    shapedBasedSameShape]

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext
      (.assign .local "missing" (.const 7))) =
      some "variable missing is not in scope in top-level declaration\n" := by
  decide +kernel

example :
    staticResultErrorMessage (checkLocalVar checkerContext "missing") =
      some "variable missing is not in scope in top-level declaration\n" := by
  decide +kernel

example :
    staticResultLocation (checkProg (α := Nat) checkerContext
      (.seq (.annot "location" "body") (.skip))) = some "AT body: " := by
  decide +kernel

example :
    staticResultErrorMessage (checkLocalVar checkerContext "missing") =
      some "variable missing is not in scope in top-level declaration\n" := by
  decide +kernel

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext (.break)) =
      some "break statement outside loop in top-level declaration\n" := by
  decide +kernel

example :
    staticResultOk (checkProg (α := Nat) checkerContext
      (.dec "y" .one (.const 7) (.return (.var .local "y")))) = false := by
  simp [staticResultOk, checkProg, checkExp, staticError, staticOk, staticBind,
    checkRedecVar, checkShape, checkerContext, lookupInfo, checkLocalVar,
    shapedBasedHasShape]

example :
    staticResultOk (checkProg (α := Nat) checkerFunctionContext
      (.dec "y" .one (.const 7) (.return (.var .local "y")))) = true := by
  decide +kernel

example :
    checkProg (α := Nat) checkerCallContext (.call none "f" []) =
      staticError (.general (getImplementationErrorMessage
        "tail call found outside function scope" "" Scope.topLevel)) := by
  simp [checkProg, checkerCallContext, checkerContext, staticError,
    getImplementationErrorMessage]

example :
    checkProg (α := Nat) checkerCallContext
      (.call (some (none, none)) "f" []) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkCallDestination,
    checkCallDestinationScope, staticOk, staticBind,
    checkFunctionName, checkFuncArgs, checkerCallContext, checkerContext,
    lookupInfo]

example :
    staticResultOk (checkProg (α := Nat) checkerCallContext
      (.call (some (some (.local, "x"), none)) "f" [])) = true := by
  decide +kernel

example :
  staticResultErrorMessage
      (checkProg (α := Nat) checkerContext (.call none "missing" [])) =
    some "tail call found outside function scope in top-level declaration\nthis should never happen. please report to a compiler developer\n" := by
  decide +kernel

example :
    checkProg (α := Nat) checkerArgContext
      (.call none "f" [.const 1]) =
      staticError (.general (getImplementationErrorMessage
        "tail call found outside function scope" "" Scope.topLevel)) := by
  simp [checkProg, checkerArgContext, checkerContext, staticError,
    getImplementationErrorMessage]

example :
    staticResultOk (checkProg (α := Nat) checkerPrimitiveContext
      (.primitive "carry" .addCarry [.const 1, .const 2, .const 0])) =
      true := by
  decide +kernel

example :
    staticResultOk (checkProg (α := Nat) checkerHandlerContext
      (.call (some (none, some ("E", "exceptionValue", .skip))) "f" [])) =
      true := by
  decide +kernel

example :
    staticResultOk (checkProg (α := Nat) checkerCallContext
      (.decCall "result" .one "f" [] .skip)) =
      true := by
  decide +kernel

example :
    staticResultOk (checkProg (α := Nat) checkerContext
      (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4))) =
      true := by
  decide +kernel

example :
    staticResultOk (checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1), ("right", .const 2)])) = true := by
  decide +kernel

example :
    staticResultErrorMessage (checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1)])) =
      some "missing field right in named struct Pair constant in top-level declaration\n" := by
  decide +kernel

end Flapjack
