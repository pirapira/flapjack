import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsNameCorrectnessParity

open Flapjack

/-! Regression for the tagged HOL lemmas `fperm_decs_decls`
    (`pan_globalsProofScript.sml:2023`) and `new_main_name_correct`
    (`pan_globalsProofScript.sml:2073`). -/

def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration,
   .decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T")]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T")]

theorem fpermDecsDeclsFixture :
    globalRenameDecls "f" "b" nonFunctionDeclarations =
      nonFunctionDeclarations :=
  fperm_decs_decls "f" "b" nonFunctionDeclarations []
    (by simp [nonFunctionDeclarations, globalDeclIsFunction])

theorem newMainNameCorrectFixture :
    globalNewMainName declarations ∈
        (functions declarations).map (fun entry => entry.1) → False :=
  new_main_name_correct declarations

def nameCorrectnessGuard : Bool :=
  ((globalFunctionNames (globalRenameDecls "f" "b" nonFunctionDeclarations)) ==
      []) &&
    !(((functions declarations).map (fun entry => entry.1)).contains
      (globalNewMainName declarations))

#guard nameCorrectnessGuard

def runChecks : IO Bool := do
  let ok ←
    if nameCorrectnessGuard then
      IO.println "PASS pan_globals fperm_decs_decls and new_main_name_correct"
      pure true
    else
      pure false
  pure ok

end Flapjack.Test.PanGlobalsNameCorrectnessParity