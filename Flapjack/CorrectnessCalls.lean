import Flapjack.Correctness

/-!
# Source-to-Loop call correctness

This module states a first reusable semantic contract for calls at the
Pancake-to-Crepe-to-Loop boundary.  The earlier call coverage was executable
only: it checked one concrete image with `#guard`.  The theorem below keeps
the caller and callee compiler contexts explicit and quantifies over the
callee's returned word.
-/

namespace Flapjack

def identityCallDeclarations (value : α) : List (Decl α) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id" [.const value]
        (.return (.var .local "result")), returnShape := .one }]

def identityCallCompileContext [OfNat α 0] : CompileContext α :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 0 }

def identityCallLoopState : LoopState α :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def identityCallSourceFunctions : List (FunName × List VarName × Prog α) :=
  [("id", ["x"], .return (.var .local "x"))]

def identityCallSourceMain (value : α) : Prog α :=
  .decCall "result" .one "id" [.const value]
    (.return (.var .local "result"))

theorem compilePanToLoop_identity_call_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (value : α) :
    (do
      let functions := pipelineLoopFunctions .rv64i 1
        (compileToCrepe identityCallCompileContext
          (identityCallDeclarations value))
      let (_, main) ← lookupLoopFunction 2 functions
      let result ← evalLoopProgWithFunctions functions 60
        identityCallLoopState main
      pure (loopResultValues result)) =
      (evalPanProgWithCalls identityCallSourceFunctions 20
        (fun _ => none) (identityCallSourceMain value)).map
        (fun result => result.2) := by
  simp [pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineFunctionInfos, compileToCrepe, compileFunctions, compileFunDecl,
    compileParamVars, functionInfos, compileProg, compileExp,
    allocatedNames, compileArgs, nestedDecs,
    loopCompileProg, loopCompileExp,
    loopCompileExps, loopCompileExp.loopCompileExps, loopNestedSeq, loopTempNames,
    loopAssignTemps, identityCallDeclarations, identityCallCompileContext,
    identityCallLoopState, identityCallSourceFunctions,
    identityCallSourceMain, evalLoopProgWithFunctions, evalLoopCall,
    evalLoopProg, evalLoopExp, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopResultValues,
    evalPanProgWithCalls, evalPanCallWithCalls, evalPanExps, evalPanExp,
    bindPanParameters, lookupPanFunction, lookupLoopFunction, lookupInfo,
    updatePanLocal]

end Flapjack
