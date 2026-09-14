import Flapjack.PanGlobals

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

end Flapjack.Test.PanLangFunctionsParity
