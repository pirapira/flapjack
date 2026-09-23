import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileDecsStructuralParity

open Flapjack

def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration, .decl .one "g" (.const 7), .name "S" [],
   .exnDecl "E" .one]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one]

theorem compileDecsEveryIsFunctionFixture :
    (globalCompileDecs compileContext declarations).functions.all
      globalDeclIsFunction = true :=
  compile_decs_EVERY_is_function compileContext declarations

theorem compileDecsDeclsThmFixture :
    (globalCompileDecs compileContext nonFunctionDeclarations).functions = [] :=
  compile_decs_decls_thm compileContext nonFunctionDeclarations
    (by simp [nonFunctionDeclarations, globalDeclIsFunction])

theorem compileDecsExnsAreExnsFixture :
    (globalCompileDecs compileContext declarations).exceptions =
      globalDeclsFilter globalDeclIsException declarations :=
  compile_decs_exns_are_exns compileContext declarations

theorem compileDecsPreserveFunctionsFixture :
    (functions (globalCompileDecs compileContext declarations).functions).map
        (fun entry => entry.1) =
      (functions declarations).map (fun entry => entry.1) :=
  compile_decs_preserve_functions compileContext declarations

def compileDecsStructuralGuard : Bool :=
  let result := globalCompileDecs compileContext declarations
  result.functions.all globalDeclIsFunction &&
  (globalCompileDecs compileContext nonFunctionDeclarations).functions.isEmpty &&
  result.exceptions.length ==
    (globalDeclsFilter globalDeclIsException declarations).length &&
  ((functions result.functions).map (fun entry => entry.1) ==
    (functions declarations).map (fun entry => entry.1))

#eval compileDecsStructuralGuard
#guard compileDecsStructuralGuard

def runChecks : IO Bool := do
  if compileDecsStructuralGuard then
    IO.println "PASS pan_globals compile_decs structural lemmas"
    pure true
  else
    IO.println "FAIL pan_globals compile_decs structural lemmas"
    pure false

end Flapjack.Test.PanGlobalsCompileDecsStructuralParity