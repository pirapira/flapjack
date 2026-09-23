import Flapjack.Pancake.PanGlobals

/-!
# Pancake `functions` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_functions_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:319-328`.
-/

namespace Flapjack.Test.PanLangFunctionsParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:319-328 (functions_def)"

def functionDeclaration : Decl Nat :=
  .function
    { name := "f"
      inline := true
      exported := false
      params := [("x", .one)]
      body := .skip
      returnShape := .one }

def globalDeclaration : Decl Nat := .decl .one "g" (.const 7)

def parityGuard : Bool :=
  (match functionEntries ([] : List (Decl Nat)) with
  | [] => true
  | _ => false) &&
  (match functionEntries [functionDeclaration] with
  | [("f", [("x", .one)], .skip, .one)] => true
  | _ => false) &&
  (match functionEntries [globalDeclaration] with
  | [] => true
  | _ => false)

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:319-328 (functions_def)"
#eval parityGuard
#guard parityGuard

/-! The production Pancake `functions` used by the executable passes is now an
    alias of the reviewed, HOL-tagged `functionEntries`
    (`cakeml/pancake/panLangScript.sml:319-328`). This is the direct
    executable-path regression: the alias reduces by `rfl` to the tagged
    definition and yields the exact HOL-EVAL observations. -/
example : functions [functionDeclaration] = functionEntries [functionDeclaration] := rfl

def functionsAliasGuard : Bool :=
  (match functions [functionDeclaration] with
  | [("f", [("x", .one)], .skip, .one)] => true
  | _ => false) &&
  (match functions [globalDeclaration] with
  | [] => true
  | _ => false)

#eval functionsAliasGuard
#guard functionsAliasGuard

def runChecks : IO Bool := do
  if parityGuard && functionsAliasGuard then
    IO.println "PASS panLang functions definition"
    IO.println "PASS panSimp functions alias to functionEntries"
    pure true
  else
    IO.println "FAIL panLang functions definition or alias"
    pure false

end Flapjack.Test.PanLangFunctionsParity
