import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# `panSem$evaluate_decls` canonical finite-map parity

Direct original-HOL oracle rows for the canonical tagged finite-map evaluator
`PanSemStateFiniteExact.evaluateDeclsHOLFinite` (the Lean counterpart of HOL
`panSem$evaluate_decls_def`).  The oracle values are those recorded by
`scripts/hol-probes/pan_evaluate_decls_probe.out`, produced by running HOL
`panSem$evaluate_decls` on the concrete states in
`scripts/hol-probes/pan_evaluate_decls_probeScript.sml`.

The older `Flapjack/Test/PanSemEvaluateDeclsExactParity.lean` exercises the
unrestricted helper `evaluateDeclsHOLExact`; this module exercises the exact
tagged finite-map definition itself, as required for the
`fmap_as_finite_support` port.
-/

namespace Flapjack.Test.PanSemEvaluateDeclsFiniteParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL DeclHOL ProgHOL FunDeclHOL)
open Flapjack.PanSemStateFiniteExact

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty

private abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

abbrev state0 : PanSemStateFiniteExact 8 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

abbrev stateLoad : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    memory := fun a => if a = (0 : Word8) then .word 9 else .word 0
    memaddrs := fun a => a = 0 }

def functionDecl : FunDeclHOL 8 :=
  { name := ml "f"
    inline := false
    exported := false
    params := [(ml "x", ShapeHOL.one)]
    body := ProgHOL.skip
    returnShape := ShapeHOL.one }

def wordOfLocal (state : PanSemStateFiniteExact 8 Unit) (name : String) : Option Nat :=
  match state.locals.lookup (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def wordOfGlobal (state : PanSemStateFiniteExact 8 Unit) (name : String) : Option Nat :=
  match state.globals.lookup (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def eshapeIsOne (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  match state.eshapes.lookup (ml name) with
  | some ShapeHOL.one => true
  | _ => false

def codeIsExpected (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  match state.code.lookup (ml name) with
  | some (params, body, returnShape) =>
      (params.length == 1) &&
        (match params with
         | [(parameterName, parameterShape)] =>
             (parameterName == ml "x") &&
               (match parameterShape with | ShapeHOL.one => true | _ => false)
         | _ => false) &&
        (match body with | ProgHOL.skip => true | _ => false) &&
        (match returnShape with | ShapeHOL.one => true | _ => false)
  | none => false

/-- `evaluate_decls s [] = SOME s`. -/
def emptyGuard : Bool :=
  (evaluateDeclsHOLFinite state0 ([] : List (DeclHOL 8))).isSome

/-- Oracle `name_noop`: a `Name` declaration leaves the state unchanged. -/
def nameNoopGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.name (ml "S") []] with
  | some result =>
      (result.globals.lookup (ml "g")).isNone &&
        (result.locals.lookup (ml "x")).isNone &&
        (result.code.lookup (ml "f")).isNone && result.structs.isEmpty
  | none => false

/-- Oracle `decl_global_update`: `SOME (ValWord 7w), FEMPTY`. -/
def declGlobalUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)] with
  | some result => wordOfGlobal result "g" == some 7 && (wordOfLocal result "x").isNone
  | none => false

/-- Oracle `decl_word_load_update`: `SOME (ValWord 9w)`. -/
def declWordLoadUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite stateLoad
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.load ShapeHOL.one (ExpHOL.const 0))] with
  | some result => wordOfGlobal result "g" == some 9
  | none => false

/-- Oracle `decl_shape_failure`: mismatched declared shape fails. -/
def declShapeFailureGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.decl (ShapeHOL.named (ml "Missing")) (ml "g") (ExpHOL.const 7)]).isNone

/-- Oracle `function_code_update`: `SOME ([("x",One)],Skip,One)`. -/
def functionCodeUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.function functionDecl] with
  | some result => codeIsExpected result "f"
  | none => false

/-- Oracle `function_bad_param_shape`: a bad parameter shape fails. -/
def functionBadParamShapeGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.function { functionDecl with
        params := [(ml "x", ShapeHOL.named (ml "Missing"))] }]).isNone

/-- Oracle `exn_shape_update`: `SOME One`. -/
def exnShapeUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.exnDecl (ml "E") ShapeHOL.one] with
  | some result => eshapeIsOne result "E"
  | none => false

/-- Oracle `exn_bad_shape_failure`: a bad exception shape fails. -/
def exnBadShapeFailureGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.exnDecl (ml "E") (ShapeHOL.named (ml "Missing"))]).isNone

def evaluateDeclsFiniteGuard : Bool :=
  emptyGuard && nameNoopGuard && declGlobalUpdateGuard && declWordLoadUpdateGuard &&
    declShapeFailureGuard && functionCodeUpdateGuard && functionBadParamShapeGuard &&
    exnShapeUpdateGuard && exnBadShapeFailureGuard

#eval emptyGuard
#eval nameNoopGuard
#eval declGlobalUpdateGuard
#eval declWordLoadUpdateGuard
#eval functionCodeUpdateGuard
#eval exnShapeUpdateGuard

#guard emptyGuard
#guard nameNoopGuard
#guard declGlobalUpdateGuard
#guard declWordLoadUpdateGuard
#guard declShapeFailureGuard
#guard functionCodeUpdateGuard
#guard functionBadParamShapeGuard
#guard exnShapeUpdateGuard
#guard exnBadShapeFailureGuard
#guard evaluateDeclsFiniteGuard

def runChecks : IO Bool := do
  if evaluateDeclsFiniteGuard then
    IO.println "PASS canonical finite panSem evaluate_decls matches HOL oracle rows"
    pure true
  else
    IO.println "FAIL canonical finite panSem evaluate_decls matches HOL oracle rows"
    pure false

end Flapjack.Test.PanSemEvaluateDeclsFiniteParity
