import Flapjack.PanGlobals

/-!
# Pancake `is_function` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_is_function_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:314-317`.
-/

namespace Flapjack.Test.PanLangIsFunctionParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:314-317 (is_function_def)"

def functionDeclaration : Decl Nat :=
  .function
    { name := "f"
      inline := true
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def globalDeclaration : Decl Nat := .decl .one "g" (.const 7)

def parityGuard : Bool :=
  globalDeclIsFunction functionDeclaration &&
  !globalDeclIsFunction globalDeclaration

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:314-317 (is_function_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangIsFunctionParity
