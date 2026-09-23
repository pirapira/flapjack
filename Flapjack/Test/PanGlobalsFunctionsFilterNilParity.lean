import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsFunctionsFilterNilParity

open Flapjack

/-! Executable regression for the exact `pan_globalsProofScript.sml:2967`
    lemma `functions_filter_nil` and the adjacent `:2042`
    `functions_FILTER_exn_decl` / `:2049` `functions_FILTER_is_name`, ported in
    `Flapjack.Pancake.Proofs.PanGlobals`. -/

def declarations : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one },
   .name "S" [], .exnDecl "E" (.named "T"),
   .decl .one "h" (.const 9)]

theorem functionsFilterNilFixture :
    functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) = [] :=
  functions_filter_nil declarations

theorem functionsFilterExnDeclFixture :
    functions (globalDeclsFilter isExnDecl declarations) = [] :=
  functions_FILTER_exn_decl declarations

theorem functionsFilterIsNameFixture :
    functions (globalDeclsFilter isName declarations) = [] :=
  functions_FILTER_is_name declarations

def functionsFilterNilGuard : Bool :=
  (functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations)).isEmpty &&
    (functions (globalDeclsFilter isExnDecl declarations)).isEmpty &&
    (functions (globalDeclsFilter isName declarations)).isEmpty

#guard functionsFilterNilGuard

/-! Regression for Cake's `MEM_functions` (`pan_globalsProofScript.sml:2380`),
    ported in `Flapjack.Pancake.Proofs.PanGlobals`: the unique function entry
    of `declarations` comes from the source `.function` declaration. -/
theorem memFunctionsFixture :
    ∃ declaration : FunDecl Nat,
      (.function declaration : Decl Nat) ∈ declarations ∧
        ("f", [], (.skip : Prog Nat), .one) =
          (declaration.name, declaration.params, declaration.body,
            declaration.returnShape) :=
  MEM_functions (declarations := declarations)
    (entry := ("f", [], (.skip : Prog Nat), .one))
    (by simp [declarations, functions, functionEntries])

def memFunctionsGuard : Bool :=
  (functions declarations).length = 1

#guard memFunctionsGuard

def runChecks : IO Bool := do
  let nilOk ←
    if functionsFilterNilGuard then
      IO.println "PASS pan_globals functions FILTER nil lemmas"
      pure true
    else
      IO.println "FAIL pan_globals functions FILTER nil lemmas"
      pure false
  let memOk ←
    if memFunctionsGuard then
      IO.println "PASS pan_globals MEM_functions"
      pure true
    else
      IO.println "FAIL pan_globals MEM_functions"
      pure false
  pure (nilOk && memOk)

end Flapjack.Test.PanGlobalsFunctionsFilterNilParity