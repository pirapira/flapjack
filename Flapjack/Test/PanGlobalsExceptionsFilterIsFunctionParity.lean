import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsExceptionsFilterIsFunctionParity

open Flapjack

/-! Executable regression for the exact `pan_globalsProofScript.sml:2515`
    theorem `exceptions_FILTER_is_function`, ported in
    `Flapjack.Pancake.Proofs.PanGlobals`. -/

def declarations : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one },
   .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]

theorem exceptionsFilterIsFunctionFixture :
    exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) = [] :=
  (exceptions_FILTER_is_function declarations).1

def exceptionsFilterIsFunctionGuard : Bool :=
  (match exceptionEntries
      (globalDeclsFilter globalDeclIsFunction declarations) with
   | [] => true
   | _ => false) &&
    (match exceptionEntries
        (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
          declarations) with
     | [("E", .named "T")] => true
     | _ => false) &&
    (match exceptionEntries
        (globalDeclsFilter globalDeclIsException declarations) with
     | [("E", .named "T")] => true
     | _ => false) &&
    (match exceptionEntries
        (globalDeclsFilter globalDeclIsName declarations) with
     | [] => true
     | _ => false) &&
    (match exceptionEntries
        (globalDeclsFilter globalDeclIsGlobal declarations) with
     | [] => true
     | _ => false)

#guard exceptionsFilterIsFunctionGuard

def runChecks : IO Bool := do
  let ok ←
    if exceptionsFilterIsFunctionGuard then
      IO.println "PASS pan_globals exceptions_FILTER_is_function"
      pure true
    else
      IO.println "FAIL pan_globals exceptions_FILTER_is_function"
      pure false
  pure ok

end Flapjack.Test.PanGlobalsExceptionsFilterIsFunctionParity