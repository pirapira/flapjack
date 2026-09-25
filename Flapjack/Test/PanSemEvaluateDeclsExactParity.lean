import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact

namespace Flapjack.Test.PanSemEvaluateDeclsExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL DeclHOL ProgHOL FunDeclHOL)

/-- Direct original-HOL `evaluate_decls` row check against
    `scripts/hol-probes/pan_evaluate_decls_probe.out` (16 rows). The oracle was
    produced by running HOL `panSem$evaluate_decls` on the concrete states in
    `scripts/hol-probes/pan_evaluate_decls_probeScript.sml`. -/

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

abbrev state0 : PanSemStateExact 8 Unit :=
  { locals := fun _ => none
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
    topAddr := 100 }

abbrev stateLoad : PanSemStateExact 8 Unit :=
  { state0 with
    memory := fun a => if a = (0 : Word8) then .word 9 else .word 0
    memaddrs := fun a => a = 0 }

abbrev stateLocals : PanSemStateExact 8 Unit :=
  { state0 with
    locals := fun name => if name = ml "x" then some (.val (.word 3)) else none }

abbrev stateCodeF : PanSemStateExact 8 Unit :=
  { state0 with
    code := fun name => if name = ml "f" then some ([], ProgHOL.skip, ShapeHOL.one) else none }

abbrev stateEshapeE : PanSemStateExact 8 Unit :=
  { state0 with
    eshapes := fun name => if name = ml "E" then some ShapeHOL.one else none }

def functionDecl : FunDeclHOL 8 :=
  { name := ml "f"
    inline := false
    exported := false
    params := [(ml "x", ShapeHOL.one)]
    body := ProgHOL.skip
    returnShape := ShapeHOL.one }

def wordOfLocal (state : PanSemStateExact 8 Unit) (name : String) : Option Nat :=
  match state.locals (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def wordOfGlobal (state : PanSemStateExact 8 Unit) (name : String) : Option Nat :=
  match state.globals (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def structsEmpty (state : PanSemStateExact 8 Unit) : Bool := state.structs.isEmpty

def eshapeIsOne (state : PanSemStateExact 8 Unit) (name : String) : Bool :=
  match state.eshapes (ml name) with
  | some ShapeHOL.one => true
  | _ => false

def codeIsExpected (state : PanSemStateExact 8 Unit) (name : String) : Bool :=
  match state.code (ml name) with
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

def emptyGuard : Bool :=
  (evaluateDeclsHOLExact state0 ([] : List (DeclHOL 8))).isSome

def nameNoopGuard : Bool :=
  let result := (evaluateDeclsHOLExact state0 [DeclHOL.name (ml "S") []]).getD state0
  structsEmpty result && (wordOfGlobal result "g").isNone && (wordOfLocal result "x").isNone &&
    (result.code (ml "f")).isNone

def declGlobalUpdateGuard : Bool :=
  let result :=
    (evaluateDeclsHOLExact state0 [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)]).getD state0
  wordOfGlobal result "g" == some 7 && (wordOfLocal result "x").isNone

def declWordLoadUpdateGuard : Bool :=
  let result :=
    (evaluateDeclsHOLExact stateLoad
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.load ShapeHOL.one (ExpHOL.const 0))]).getD state0
  wordOfGlobal result "g" == some 9

def declBadLoadShapeGuard : Bool :=
  (evaluateDeclsHOLExact state0
    [DeclHOL.decl ShapeHOL.one (ml "g")
      (ExpHOL.load (ShapeHOL.named (ml "Missing")) (ExpHOL.const 0))]).isNone

def declPreservesLocalsGuard : Bool :=
  let result :=
    (evaluateDeclsHOLExact stateLocals [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)]).getD state0
  wordOfGlobal result "g" == some 7 && wordOfLocal result "x" == some 3

def declLeftToRightGuard : Bool :=
  let result :=
    (evaluateDeclsHOLExact state0
      [ DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)
      , DeclHOL.decl ShapeHOL.one (ml "h") (ExpHOL.var VarKind.global (ml "g")) ]).getD state0
  wordOfGlobal result "g" == some 7 && wordOfGlobal result "h" == some 7

def declEmptyLocalsFailureGuard : Bool :=
  (evaluateDeclsHOLExact stateLocals
    [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.var VarKind.local (ml "x"))]).isNone

def declShapeFailureGuard : Bool :=
  (evaluateDeclsHOLExact state0
    [DeclHOL.decl (ShapeHOL.named (ml "Missing")) (ml "g") (ExpHOL.const 7)]).isNone

def functionCodeUpdateGuard : Bool :=
  let result := (evaluateDeclsHOLExact state0 [DeclHOL.function functionDecl]).getD state0
  codeIsExpected result "f"

def functionCodeReplacementGuard : Bool :=
  let result := (evaluateDeclsHOLExact stateCodeF [DeclHOL.function functionDecl]).getD state0
  codeIsExpected result "f"

def functionBadParamShapeGuard : Bool :=
  (evaluateDeclsHOLExact state0
    [DeclHOL.function { functionDecl with params := [(ml "x", ShapeHOL.named (ml "Missing"))] }]).isNone

def functionBadReturnShapeGuard : Bool :=
  (evaluateDeclsHOLExact state0
    [DeclHOL.function { functionDecl with returnShape := ShapeHOL.named (ml "Missing") }]).isNone

def exnShapeUpdateGuard : Bool :=
  let result := (evaluateDeclsHOLExact state0 [DeclHOL.exnDecl (ml "E") ShapeHOL.one]).getD state0
  eshapeIsOne result "E"

def exnDuplicateFailureGuard : Bool :=
  (evaluateDeclsHOLExact stateEshapeE [DeclHOL.exnDecl (ml "E") ShapeHOL.one]).isNone

def exnBadShapeFailureGuard : Bool :=
  (evaluateDeclsHOLExact state0
    [DeclHOL.exnDecl (ml "E") (ShapeHOL.named (ml "Missing"))]).isNone

def evaluateDeclsExactGuard : Bool :=
  emptyGuard && nameNoopGuard && declGlobalUpdateGuard && declWordLoadUpdateGuard &&
    declBadLoadShapeGuard && declPreservesLocalsGuard && declLeftToRightGuard &&
    declEmptyLocalsFailureGuard && declShapeFailureGuard && functionCodeUpdateGuard &&
    functionCodeReplacementGuard && functionBadParamShapeGuard && functionBadReturnShapeGuard &&
    exnShapeUpdateGuard && exnDuplicateFailureGuard && exnBadShapeFailureGuard

#eval emptyGuard
#eval declGlobalUpdateGuard
#eval functionCodeUpdateGuard
#eval exnShapeUpdateGuard
#guard emptyGuard
#guard nameNoopGuard
#guard declGlobalUpdateGuard
#guard declWordLoadUpdateGuard
#guard declBadLoadShapeGuard
#guard declPreservesLocalsGuard
#guard declLeftToRightGuard
#guard declEmptyLocalsFailureGuard
#guard declShapeFailureGuard
#guard functionCodeUpdateGuard
#guard functionCodeReplacementGuard
#guard functionBadParamShapeGuard
#guard functionBadReturnShapeGuard
#guard exnShapeUpdateGuard
#guard exnDuplicateFailureGuard
#guard exnBadShapeFailureGuard
#guard evaluateDeclsExactGuard

def runChecks : IO Bool := do
  if evaluateDeclsExactGuard then
    IO.println "PASS exact panSem evaluate_decls (16 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem evaluate_decls (16 HOL rows)"
    pure false

end Flapjack.Test.PanSemEvaluateDeclsExactParity
