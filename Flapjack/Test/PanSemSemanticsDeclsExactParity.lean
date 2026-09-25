/-
Copyright (c) 2026 Flapjack contributors.

Parity for the exact `panSem$semantics_decls` control flow.

The direct original-HOL oracle rows live in
`scripts/hol-probes/pan_sem_e2e_probe.out`:
`semantics_decls_bad_struct=Fail`, `semantics_decls_bad_function=Fail`,
`semantics_decls_bad_exception=Fail`.

Because `semanticsDeclsHOLExact` is parameterised by the `Fail` outcome and the
final `semantics` call (the exact `semantics_def` port has not landed), the
fixtures instantiate the outcome with `Bool`: the failure branch is `false` and
the continuation is constantly `true`, so each HOL `Fail` row corresponds to a
`false` result and the success branch to `true`.
-/

import Flapjack.Pancake.Semantics.PanSem.SemanticsDeclsExact

namespace Flapjack.Test.PanSemSemanticsDeclsExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL DeclHOL FunDeclHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

abbrev state0 : PanSemStateExact 8 Unit where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

abbrev badStructDecls : List (DeclHOL 8) :=
  [.name (ml "S") [(ml "f", ShapeHOL.named (ml "Missing"))]]

abbrev badFunctionDecls : List (DeclHOL 8) :=
  [.function { name := ml "f", inline := false, exported := false,
               params := [(ml "x", ShapeHOL.named (ml "Missing"))],
               body := ProgHOL.skip, returnShape := ShapeHOL.one }]

abbrev badExceptionDecls : List (DeclHOL 8) :=
  [.exnDecl (ml "E") (ShapeHOL.named (ml "Missing"))]

/-- HOL `semantics_decls_bad_struct=Fail` (`decs_stcnames` rejects the unknown field shape). -/
def badStructGuard : Bool :=
  semanticsDeclsHOLExact state0 (ml "main") badStructDecls false (fun _ _ => true) == false

/-- HOL `semantics_decls_bad_function=Fail` (`evaluate_decls` rejects the unknown parameter shape). -/
def badFunctionGuard : Bool :=
  semanticsDeclsHOLExact state0 (ml "main") badFunctionDecls false (fun _ _ => true) == false

/-- HOL `semantics_decls_bad_exception=Fail` (`evaluate_decls` rejects the unknown exception shape). -/
def badExceptionGuard : Bool :=
  semanticsDeclsHOLExact state0 (ml "main") badExceptionDecls false (fun _ _ => true) == false

/-- Success branch: the empty declaration list scans and evaluates, then hands off to `semantics`. -/
def emptyDeclsGuard : Bool :=
  semanticsDeclsHOLExact state0 (ml "main") [] false (fun _ _ => true) == true

def semanticsDeclsGuard : Bool :=
  badStructGuard && badFunctionGuard && badExceptionGuard && emptyDeclsGuard

#guard badStructGuard
#guard badFunctionGuard
#guard badExceptionGuard
#guard emptyDeclsGuard
#guard semanticsDeclsGuard

example : semanticsDeclsHOLExact state0 (ml "main") badStructDecls false (fun _ _ => true) = false :=
  semanticsDeclsHOLExact_decs_none state0 (ml "main") badStructDecls false (fun _ _ => true)
    (by decide)

example : semanticsDeclsHOLExact state0 (ml "main") badFunctionDecls false (fun _ _ => true) = false :=
  semanticsDeclsHOLExact_evaluate_none state0 (ml "main") badFunctionDecls false (fun _ _ => true) []
    rfl (by decide)

example : semanticsDeclsHOLExact state0 (ml "main") badExceptionDecls false (fun _ _ => true) = false :=
  semanticsDeclsHOLExact_evaluate_none state0 (ml "main") badExceptionDecls false (fun _ _ => true) []
    rfl (by decide)

example : semanticsDeclsHOLExact state0 (ml "main") [] false (fun _ _ => true) = true :=
  semanticsDeclsHOLExact_ok state0 (ml "main") [] false (fun _ _ => true) [] { state0 with structs := [] }
    rfl rfl

def runChecks : IO Bool := do
  if semanticsDeclsGuard then
    IO.println "PASS exact panSem semantics_decls control flow (3 Fail rows + success branch)"
    pure true
  else
    IO.println "FAIL exact panSem semantics_decls control flow (3 Fail rows + success branch)"
    pure false

end Flapjack.Test.PanSemSemanticsDeclsExactParity
