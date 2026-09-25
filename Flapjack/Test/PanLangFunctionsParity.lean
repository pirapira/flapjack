import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl

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

/-! ## Checked codec bridge `functionsHOL` → `functionEntries` (bead flapjack-ni1.2)

The tagged `functionsHOL` (`Flapjack/Pancake/PanLang/Decl.lean`) projects the
`Function` entries of a word-indexed `DeclHOL list`; the production
`functionEntries` projects the same entries from a generic `Decl α list`.  The
bridge `functionsHOL_map_funEntryOfHOL` maps the resulting tuples componentwise
through `toStringOfBytes`/`paramOfHOL`/`progOfHOL`/`shapeOfHOL`.  Direct
executable routing is unavailable because the carriers differ (word-indexed
`DeclHOL`/`MlS`/`ShapeHOL`/`ProgHOL` versus polymorphic `Decl α`/`String`), so
this checked relation is the connection. -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def functionDeclHOL : DeclHOL 8 :=
  .function
    { name := ofString "f"
      inline := true
      exported := false
      params := [(ofString "x", .one)]
      body := .skip
      returnShape := .one }

def globalDeclHOL : DeclHOL 8 :=
  .decl .one (ofString "g") (.const 7)

example :
    (functionsHOL [functionDeclHOL, globalDeclHOL]).map funEntryOfHOL =
      functionEntries ([functionDeclHOL, globalDeclHOL].map declOfHOL) :=
  functionsHOL_map_funEntryOfHOL _

example :
    (functionsHOL [globalDeclHOL]).map funEntryOfHOL =
      (functionEntries [declOfHOL globalDeclHOL]) :=
  functionsHOL_map_funEntryOfHOL [globalDeclHOL]

def functionsHOLBridgeGuard : Bool :=
  (match (functionsHOL [functionDeclHOL, globalDeclHOL]).map funEntryOfHOL with
  | [("f", [("x", .one)], .skip, .one)] => true
  | _ => false) &&
  (match (functionsHOL [globalDeclHOL]).map funEntryOfHOL with
  | [] => true
  | _ => false)

#guard functionsHOLBridgeGuard

end Flapjack.Test.PanLangFunctionsParity
