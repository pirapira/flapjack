import Flapjack.Pancake.PanToTarget
/-!
Kernel replay of the eight original HOL control observations in
`scripts/hol-probes/pan_to_target_source_probe.out`. The main-name oracle
observes the actual original compile_prog first LET argument, and the exported
name oracle evaluates the original exports definition. Native checks below
also retain the complete source declarations when moving or inserting main.
These are source-control observations, not executed compiler or machine
semantics parity claims.
-/
set_option autoImplicit false
namespace Flapjack.Test.PanToTargetSourceParity
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanToTarget
private def mainDecl : DeclHOL 32 := .function
  { name := ofString "main", inline := false, exported := false, params := [],
    body := .return (.const 0), returnShape := .one }
private def exportDecl (name : MlS) (exported : Bool) : DeclHOL 32 := .function
  { name := name, inline := false, exported := exported, params := [],
    body := .return (.const 0), returnShape := .one }
example : mainFirstHOL (width := 32) [] = [] := rfl
example : mainFirstHOL [.exnDecl (ofString "E") .one] =
    [mainDecl, .exnDecl (ofString "E") .one] := rfl
example : mainFirstHOL [mainDecl, .exnDecl (ofString "E") .one] =
    [mainDecl, .exnDecl (ofString "E") .one] := rfl
example : mainFirstHOL [.exnDecl (ofString "E") .one, mainDecl] =
    [mainDecl, .exnDecl (ofString "E") .one] := rfl
example : mainFirstHOL [exportDecl (ofString "f") false, exportDecl (ofString "g") false] =
    [mainDecl, exportDecl (ofString "f") false, exportDecl (ofString "g") false] := rfl
example : mainFirstHOL [exportDecl (ofString "f") false, mainDecl,
    exportDecl (ofString "g") false, exportDecl (ofString "main") true] =
    [mainDecl, exportDecl (ofString "f") false,
      exportDecl (ofString "g") false, exportDecl (ofString "main") true] := rfl
example : exportsHOL (width := 32) [] = [] := rfl
example : exportsHOL [exportDecl (ofString "f") true, .exnDecl (ofString "E") .one,
    exportDecl (ofString "hidden") false, exportDecl (ofString "f") true] =
    [ofString "f", ofString "f"] := rfl
end Flapjack.Test.PanToTargetSourceParity
