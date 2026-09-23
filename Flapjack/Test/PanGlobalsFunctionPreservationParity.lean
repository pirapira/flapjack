import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsFunctionPreservationParity

open Flapjack

/-! Regression for the tagged HOL lemmas `resort_decls_preserve_functions`
    (`pan_globalsProofScript.sml:2055`) and `fperm_decs_FILTER_is_function`
    (`pan_globalsProofScript.sml:2032`). -/

def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration,
   .decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T"),
   .decl .one "h" (.const 9)]

theorem resortDeclsPreserveFunctionsFixture :
    functions (globalResortDecls declarations) = functions declarations :=
  resort_decls_preserve_functions declarations

theorem fpermDecsFilterIsFunctionFixture :
    globalRenameDecls "f" "b"
        (globalDeclsFilter globalDeclIsFunction declarations) =
      globalDeclsFilter globalDeclIsFunction
        (globalRenameDecls "f" "b" declarations) :=
  fperm_decs_FILTER_is_function "f" "b" declarations

def functionPreservationGuard : Bool :=
  ((functions (globalResortDecls declarations)).map (fun entry => entry.1) ==
      ["f"]) &&
    ((functions (globalRenameDecls "f" "b"
        (globalDeclsFilter globalDeclIsFunction declarations))).map
      (fun entry => entry.1) == ["b"])

#guard functionPreservationGuard

def runChecks : IO Bool := do
  let ok ←
    if functionPreservationGuard then
      IO.println "PASS pan_globals function preservation lemmas"
      pure true
    else
      pure false
  pure ok

end Flapjack.Test.PanGlobalsFunctionPreservationParity