import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileDecsThreadingParity

open Flapjack

/-- The pass context used by the direct-HOL fixture
    (`scripts/hol-probes/pan_globals_compile_decs_probeScript.sml`). -/
def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 0
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-- A function whose body reads the global `g`, which is declared *after* it in
    `functionBeforeDecl`. -/
def globalFunction : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .assign .local "x" (.var .global "g"), returnShape := .one }

def functionBeforeDecl : List (Decl Nat) :=
  [globalFunction, .decl .one "g" (.const 7)]

def functionAfterDecl : List (Decl Nat) :=
  [.decl .one "g" (.const 7), globalFunction]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one]

def threadedBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionBeforeDecl

def threadedAfter : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionAfterDecl

def productionBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecs compileContext functionBeforeDecl

def threadedNonFunction : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext nonFunctionDeclarations

/-- Classifies a compiled function body: `0` is an unresolved global read
    (`Const`), `1` a resolved one (`Load`), `2` anything else. -/
def bodyKind : Prog Nat → Nat
  | .assign _ _ (.const _) => 0
  | .assign _ _ (.load _ _) => 1
  | _ => 2

def firstFunctionBodyKind (result : GlobalCompileDecsResult Nat) : Nat :=
  match result.functions with
  | [.function function] => bodyKind function.body
  | _ => 3

/-- The HOL `function_before_decl` row: the later `g` declaration is not yet in
    scope, so the threaded pass leaves the body's global read unresolved. -/
theorem threadedBeforeBodyUnresolved : firstFunctionBodyKind threadedBefore = 0 := by
  simp [firstFunctionBodyKind, threadedBefore, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionBeforeDecl, globalCompileProg, globalCompileExp,
    compileContext, lookupInfo]

/-- The HOL `function_after_decl` row: with `g` declared first, the threaded
    pass resolves the global read. -/
theorem threadedAfterBodyResolved : firstFunctionBodyKind threadedAfter = 1 := by
  simp [firstFunctionBodyKind, threadedAfter, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionAfterDecl, globalCompileProg, globalCompileExp,
    compileContext, globalAddress, lookupInfo]

/-- The old production pass compiles every body under the final collected
    context, so it wrongly resolves the forward reference. -/
theorem productionBeforeBodyResolved : firstFunctionBodyKind productionBefore = 1 := by
  simp [firstFunctionBodyKind, productionBefore, bodyKind, globalFunction,
    functionBeforeDecl, globalCompileProg, globalCompileExp, compileContext,
    globalCompileDecs, globalCollect, globalCompileInitializers,
    globalCompileDecls, globalDeclsFilter, globalDeclIsFunction, globalAddress,
    lookupInfo]

theorem threadedEveryIsFunction :
    threadedBefore.functions.all globalDeclIsFunction = true :=
  compile_decs_EVERY_is_function_threaded compileContext functionBeforeDecl
    threadedBefore.initializers threadedBefore.functions
    threadedBefore.exceptions threadedBefore.context rfl

theorem threadedDeclsThm : threadedNonFunction.functions = [] :=
  compile_decs_decls_thm_threaded compileContext nonFunctionDeclarations
    threadedNonFunction.initializers threadedNonFunction.functions
    threadedNonFunction.exceptions threadedNonFunction.context rfl
    (by simp [nonFunctionDeclarations, globalDeclIsFunction])

theorem threadedAppend :
    globalCompileDecsThreaded compileContext (functionBeforeDecl ++ [.exnDecl "E" .one]) =
      let first := globalCompileDecsThreaded compileContext functionBeforeDecl
      let second := globalCompileDecsThreaded first.context [.exnDecl "E" .one]
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } :=
  compile_decls_append_threaded compileContext functionBeforeDecl [.exnDecl "E" .one]

def threadingGuard : Bool :=
  firstFunctionBodyKind threadedBefore == 0 &&
  firstFunctionBodyKind threadedAfter == 1 &&
  firstFunctionBodyKind productionBefore == 1 &&
  threadedBefore.functions.all globalDeclIsFunction &&
  threadedNonFunction.functions.isEmpty

#eval threadingGuard
#guard threadingGuard

def runChecks : IO Bool := do
  if threadingGuard then
    IO.println "PASS pan_globals compile_decs context threading (Function before Decl)"
    pure true
  else
    IO.println "FAIL pan_globals compile_decs context threading (Function before Decl)"
    pure false

end Flapjack.Test.PanGlobalsCompileDecsThreadingParity
