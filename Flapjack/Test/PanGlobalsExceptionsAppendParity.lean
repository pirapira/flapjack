import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsExceptionsAppendParity

open Flapjack

/-! Executable regression for the exact `pan_globalsProofScript.sml:2507`
    lemma `exceptions_append`, ported in `Flapjack.Pancake.Proofs.PanGlobals`. -/

def declarations : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one },
   .name "S" [], .exnDecl "E" (.named "T")]

def rest : List (Decl Nat) := [.exnDecl "F" .one, .decl .one "k" (.const 11)]

theorem exceptionsAppendFixture :
    exceptionEntries (declarations ++ rest) =
      exceptionEntries declarations ++ exceptionEntries rest :=
  exceptions_append declarations rest

def exceptionsAppendGuard : Bool :=
  (match exceptionEntries (declarations ++ rest) with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false) &&
    (match exceptionEntries declarations ++ exceptionEntries rest with
     | [("E", .named "T"), ("F", .one)] => true
     | _ => false)

#guard exceptionsAppendGuard

/-! Constructor-behavior fixture for the relocated, HOL-tagged
    `panLang$exceptions` counterpart `exceptionEntries`
    (`panLangScript.sml:328`): only `.exnDecl` contributes, preserving order. -/
def exceptionsConstructorGuard : Bool :=
  let mixed : List (Decl Nat) :=
    [.function
       { name := "f", inline := false, exported := false, params := [],
         body := .skip, returnShape := .one },
     .decl .one "h" (.const 9), .name "S" [], .exnDecl "E" (.named "T"),
     .exnDecl "F" .one]
  (match exceptionEntries mixed with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false)

#guard exceptionsConstructorGuard

def runChecks : IO Bool := do
  let appendOk ←
    if exceptionsAppendGuard then
      IO.println "PASS pan_globals exceptions_append"
      pure true
    else
      IO.println "FAIL pan_globals exceptions_append"
      pure false
  let constructorOk ←
    if exceptionsConstructorGuard then
      IO.println "PASS panLang exceptions definition"
      pure true
    else
      IO.println "FAIL panLang exceptions definition"
      pure false
  pure (appendOk && constructorOk)

end Flapjack.Test.PanGlobalsExceptionsAppendParity