import Flapjack.Test.Basics

namespace Flapjack

open RiscV

/-! Direct parity for Cake's `distinct_lists_def` (`pan_commonScript.sml:8`):
    only membership of the right-hand list matters; repetitions on the left
    remain harmless, while any shared element rejects the pair. -/
#guard distinctLists [] [1, 2] == true
#guard distinctLists [2, 4, 4] [0, 1, 3] == true
#guard distinctLists [2, 4, 4] [4, 9] == false
#guard distinctLists [0, 1] [] == true

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

#guard (compileFunDeclSource assignmentContext identityFunction).params == [0]

example :
    (compileFunDeclSource assignmentContext identityFunction).body =
      .return [.var 0] := by
  simp [compileFunDeclSource, panToCrepCompFunc, panToCrepMakeVmap,
    identityFunction, compileProg, compileExp, compileParamVars, lookupInfo]

example :
    (compileToCrep assignmentContext [.function constantFunction]).head?.map
        CompiledFunction.body =
      some (.return [.const 7]) := by
  simp [compileToCrep, compileFunctionsSource, compileFunDeclSource,
    panToCrepCompFunc, functionInfos, constantFunction, compileProg, compileExp]

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
      .dec 2 (.const 0) (.call (some ([2], none)) "f" []) := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, callContext,
    crepContext, lookupInfo, nestedDecs]

example :
    compileProg callContext
      (.call (some (none, some ("E", "missing", .skip))) "f" []) =
      .dec 2 (.const 0)
        (.call (some ([2], some (9, .seq .skip .skip))) "f" []) := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, compileProg,
    expHdlFiniteMap, callContext, crepContext, lookupInfo, nestedDecs]

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
  simp [compileProg, firstCompiledExp, compileExp, maxCrepExpVar, nestedDecs,
    assignmentContext]

example :
    compileProg assignmentContext
      (.shMemLoad .op8 .local "x" (.const 10)) =
      .shMem .load8 0 (.const 10) := by
  simp [compileProg, firstCompiledExpAnyShape, compileExp, loadMemOpHOL,
    assignmentContext, lookupInfo]

example :
    compileProg assignmentContext
      (.shMemStore .op8 (.const 10) (.const 7)) =
      .dec 1 (.const 7) (.shMem .store8 1 (.const 10)) := by
  simp [compileProg, firstCompiledExpAnyShape, compileExp, maxCrepExpVar,
    storeMemOpHOL, nestedDecs,
    assignmentContext]

/-! Cake's ExtCall/ShMemStore temporary base is the maximum variable in the
    compiled expressions, even when a stale context `vmax` is lower. -/
def highVariableContext : CompileContext Nat :=
  { assignmentContext with vars := [("x", (.one, [7]))], maxVar := 0 }

#guard
  match compileProg highVariableContext
      (.extCall "ffi" (.var .local "x") (.var .local "x")
        (.var .local "x") (.var .local "x")) with
  | .dec 8 (.var 7) (.dec 9 (.var 7) (.dec 10 (.var 7)
      (.dec 11 (.var 7) (.extCall "ffi" 8 9 10 11)))) => true
  | _ => false

#guard
  match compileProg highVariableContext
      (.shMemStore .op8 (.const 10) (.var .local "x")) with
  | .dec 1 (.var 7) (.shMem .store8 1 (.const 10)) => true
  | _ => false

/-! `pan_to_crep$compile` bases a shared-memory-store temporary on the address
    expression, not the value expression.  Keep the address deliberately at a
    higher slot so a value-based implementation is observably different. -/
def highAddressLowValueContext : CompileContext Nat :=
  { assignmentContext with
      vars := [("address", (.one, [7])), ("value", (.one, [1]))]
      maxVar := 0 }

#guard
  match compileProg highAddressLowValueContext
      (.shMemStore .op8 (.var .local "address") (.var .local "value")) with
  | .dec 8 (.var 1) (.shMem .store8 8 (.var 7)) => true
  | _ => false

def crepAddCarryHandler : CrepPrimitiveHandler Nat
  | .addCarry, [left, right, carry] => some [left + right + carry, 0]
  | _, _ => none

example :
    (evalCrepStateProgWithPrimitive crepAddCarryHandler (fun _ => none)
      (compileProg crepContext
        (.seq
          (.primitive "pair" .addCarry
            [.const (α := Nat) 1, .const 2, .const 0])
          (.return (.var .local "pair"))))).map Prod.snd =
      some [3, 0] := by
  rw [compileProg_seq]
  have hreturn : compileProg crepContext (.return (.var .local "pair")) =
      .return [.var 0, .var 1] := by
    rw [compileProg_return]
    simp [compileExp, lookupInfo, crepContext, Shape.shapeSize]
  rw [hreturn]
  decide +kernel

example :
    (loopCompileExp loopContext 3 [] (.load32 (.const (α := Nat) 8))).code =
      [.assign 3 (.const 8), .load32 3 3] := by
  simp [loopCompileExp]

example :
    loopCompileProg loopContext []
      (.return [(.const (α := Nat) 7)]) =
      .seq (.assign 3 (.const 7)) (.seq (.return [3]) .skip) := by
  simp [loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, loopContext]

example :
    loopCompileProg loopContext []
        (.store32 (.const (α := Nat) 8) (.const 255)) =
      .seq (.assign 3 (.const 8))
        (.seq (.assign 4 (.const 255))
          (.seq (.store32 3 4) .skip)) := by
  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
    loopContext]

example :
    loopToWordExp (LoopExp.baseAddr : LoopExp Nat) = some (.lookup .currHeap) := by
  simp [loopToWordExp]

example :
    loopVarsOfExp ((LoopExp.op .add [.var 1, .load (.var 2)]) : LoopExp Nat) =
      [1, 2] := by
  simp [loopVarsOfExp]

example :
    loopAssignedVars (LoopProg.seq (.assign 1 (.const 0)) (.load32 1 2)) = [1, 2] := by
  rfl

#guard
  -- `acc_vars` records assigned variables, not expression reads
  loopAccVars (LoopProg.assign 1 (.op .add [.var 2, .const 0])) [] = [1]

end Flapjack
