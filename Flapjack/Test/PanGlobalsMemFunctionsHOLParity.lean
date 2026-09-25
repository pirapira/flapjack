/-
Oracle parity for the exact HOL `panLang$functions` projection and the
`pan_globalsProof$MEM_functions` membership theorem over the exact carriers
(bead flapjack-pxn.18.3.5.8.17).

Rows reproduce `scripts/hol-probes/pan_globals_mem_functions_probe.out`:
  functions_empty=[] functions_function=[(«f»,[(«x»,One)],Skip,One)]
  functions_global=[] mem_function_entry=T
-/
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsMemFunctionsHOLParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString
private def s (str : String) : MlS := Flapjack.Basis.Pure.MlString.ofString str

private def functionDecl : DeclHOL 64 :=
  .function { name := s "f", inline := true, exported := false,
              params := [(s "x", .one)], body := .skip, returnShape := .one }

private def globalDecl : DeclHOL 64 := .decl .one (s "g") (.const 0)

private def entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  functionsHOL [globalDecl, functionDecl]

private def functionsEmptyRow : Bool := (functionsHOL ([] : List (DeclHOL 64))).isEmpty
private def functionsFunctionRow : Bool := (functionsHOL [functionDecl]).length == 1
private def functionsGlobalRow : Bool := (functionsHOL [globalDecl]).isEmpty
private def entryShapeRow : Bool :=
  match entries with
  | [(name, params, body, shape)] =>
      name.explode.length == 1 && params.length == 1 &&
        (match params with | [(p, _)] => p.explode.length == 1 | _ => false) &&
        (match body with | .skip => true | _ => false) &&
        (match shape with | .one => true | _ => false)
  | _ => false

/-- The exact membership theorem for the projected function entry. -/
example : ∃ fi : FunDeclHOL 64,
    (.function fi : DeclHOL 64) ∈ [functionDecl] ∧
      (s "f", [(s "x", .one)], ProgHOL.skip, ShapeHOL.one)
        = (fi.name, fi.params, fi.body, fi.returnShape) :=
  MEM_functionsHOL
    (entry := (s "f", [(s "x", .one)], ProgHOL.skip, ShapeHOL.one))
    (by
      simp [functionsHOL, functionDecl, List.mem_cons])

private def parityGuard : Bool :=
  functionsEmptyRow && functionsFunctionRow && functionsGlobalRow && entryShapeRow

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_globals MEM_functions (exact carriers) functions projection and membership"
    pure true
  else
    IO.println "FAIL pan_globals MEM_functions (exact carriers)"
    pure false

end Flapjack.Test.PanGlobalsMemFunctionsHOLParity
