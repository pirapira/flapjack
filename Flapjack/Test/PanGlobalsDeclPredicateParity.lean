import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsDeclPredicateParity

open Flapjack

/-! Executable regression for the exact `pan_globalsProofScript.sml:2527`
    lemma `not_is_function` and the exact `:2535` lemma `decl_distinct`,
    ported in `Flapjack.Pancake.Proofs.PanGlobals`. -/

def fixture : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one },
   .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]

theorem notIsFunctionFixture (declaration : Decl Nat) :
    (isName declaration = true → globalDeclIsFunction declaration = false) ∧
    (isDecl declaration = true → globalDeclIsFunction declaration = false) ∧
    (isExnDecl declaration = true → globalDeclIsFunction declaration = false) :=
  not_is_function declaration

theorem declDistinctFixture : ∀ declaration ∈ fixture,
    (isDecl declaration && isName declaration) = false ∧
    (isDecl declaration && globalDeclIsFunction declaration) = false ∧
    (isDecl declaration && isExnDecl declaration) = false :=
  fun declaration _ => decl_distinct declaration

def notIsFunctionGuard : Bool :=
  fixture.all (fun declaration =>
    (!isName declaration || !globalDeclIsFunction declaration) &&
    (!isDecl declaration || !globalDeclIsFunction declaration) &&
    (!isExnDecl declaration || !globalDeclIsFunction declaration))

#guard notIsFunctionGuard

def declDistinctGuard : Bool :=
  fixture.all (fun declaration =>
    !(isDecl declaration && isName declaration) &&
    !(isDecl declaration && globalDeclIsFunction declaration) &&
    !(isDecl declaration && isExnDecl declaration))

#guard declDistinctGuard

def runChecks : IO Bool := do
  let notIsFunctionOk ←
    if notIsFunctionGuard then
      IO.println "PASS pan_globals not_is_function"
      pure true
    else
      IO.println "FAIL pan_globals not_is_function"
      pure false
  let declDistinctOk ←
    if declDistinctGuard then
      IO.println "PASS pan_globals decl_distinct"
      pure true
    else
      IO.println "FAIL pan_globals decl_distinct"
      pure false
  pure (notIsFunctionOk && declDistinctOk)

end Flapjack.Test.PanGlobalsDeclPredicateParity