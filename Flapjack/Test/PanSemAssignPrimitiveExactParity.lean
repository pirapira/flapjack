import Flapjack.Pancake.Semantics.PanSem.AssignPrimitiveExact
import Flapjack.Basis.Pure.MlString

/-!
# Parity for the exact `Assign`/`Primitive` clause steps

Reproduces the direct original-HOL rows checked into
`scripts/hol-probes/pan_sem_e2e_probe.out`:

```
assign_local_ok=(NONE,SOME (ValWord 9w))
assign_global_ok=(NONE,SOME (ValWord 9w))
assign_shape_mismatch=(SOME Error,SOME (ValWord 7w))
assign_expr_error=(SOME Error,SOME (ValWord 7w))
primitive_success=(NONE,SOME (RStruct [ValWord 90w; ValWord 0w]))
primitive_shape_mismatch=(SOME Error,SOME (ValWord 7w))
primitive_wrong_args=(SOME Error,SOME (RStruct [ValWord 0w; ValWord 0w]))
primitive_arg_error=(SOME Error,SOME (RStruct [ValWord 0w; ValWord 0w]))
```
-/

namespace Flapjack.Test.PanSemAssignPrimitiveExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL)

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

abbrev assignBaseState : PanSemStateExact 64 Unit :=
  { locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
    globals := fun name => if name = ml "g" then some (.val (.word 1)) else none
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

abbrev primitiveState : PanSemStateExact 64 Unit :=
  { assignBaseState with
    locals := fun name =>
      if name = ml "x" then some (.rStruct [.val (.word 0), .val (.word 0)]) else none }

def evalExpressionFixture (state : PanSemStateExact 64 Unit) (expression : ExpHOL 64) :
    Option (ValueHOL 64) :=
  match expression with
  | .const value => some (.val (.word value))
  | .var .local name => state.locals name
  | .var .global name => state.globals name
  | _ => none

def evalExpressionsFixture (state : PanSemStateExact 64 Unit) :
    List (ExpHOL 64) → Option (List (ValueHOL 64))
  | [] => some []
  | expression :: rest =>
      match evalExpressionFixture state expression, evalExpressionsFixture state rest with
      | some value, some values => some (value :: values)
      | _, _ => none
termination_by expressions => sizeOf expressions

def isErrorResult (result : Option (PanSemResultExact 64)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def localsWord (state : PanSemStateExact 64 Unit)
    (name : Flapjack.Pancake.PanLang.MlS) : Option Nat :=
  match state.locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def globalsWord (state : PanSemStateExact 64 Unit)
    (name : Flapjack.Pancake.PanLang.MlS) : Option Nat :=
  match state.globals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def localsStructWords (state : PanSemStateExact 64 Unit)
    (name : Flapjack.Pancake.PanLang.MlS) : Option (List Nat) :=
  match state.locals name with
  | some (.rStruct values) =>
      some (values.map (fun value =>
        match value with
        | .val (.word word) => word.toNat
        | _ => 0))
  | _ => none

def assignLocalOkGuard : Bool :=
  let result := assignStepHOLExact assignBaseState .local (ml "x") (.const 9) evalExpressionFixture
  result.1.isNone && localsWord result.2 (ml "x") == some 9

def assignGlobalOkGuard : Bool :=
  let result := assignStepHOLExact assignBaseState .global (ml "g") (.const 9) evalExpressionFixture
  result.1.isNone && globalsWord result.2 (ml "g") == some 9

def assignShapeMismatchGuard : Bool :=
  let result := assignStepHOLExact assignBaseState .local (ml "x") (.rstruct []) evalExpressionFixture
  isErrorResult result.1 && localsWord result.2 (ml "x") == some 7

def assignExprErrorGuard : Bool :=
  let result := assignStepHOLExact assignBaseState .local (ml "x")
    (.var .local (ml "missing")) evalExpressionFixture
  isErrorResult result.1

def primitiveSuccessGuard : Bool :=
  let result := primitiveStepHOLExact primitiveState (ml "x") .addCarry
    [.const 40, .const 50, .const 0] evalExpressionsFixture
  result.1.isNone && localsStructWords result.2 (ml "x") == some [90, 0]

def primitiveShapeMismatchGuard : Bool :=
  let result := primitiveStepHOLExact assignBaseState (ml "x") .addCarry
    [.const 40, .const 50, .const 0] evalExpressionsFixture
  isErrorResult result.1

def primitiveWrongArgsGuard : Bool :=
  let result := primitiveStepHOLExact primitiveState (ml "x") .addCarry
    [.const 1, .const 2] evalExpressionsFixture
  isErrorResult result.1

def primitiveArgErrorGuard : Bool :=
  let result := primitiveStepHOLExact primitiveState (ml "x") .addCarry
    [.const 1, .var .local (ml "missing"), .const 0] evalExpressionsFixture
  isErrorResult result.1

def assignPrimitiveGuard : Bool :=
  assignLocalOkGuard && assignGlobalOkGuard && assignShapeMismatchGuard && assignExprErrorGuard &&
    primitiveSuccessGuard && primitiveShapeMismatchGuard && primitiveWrongArgsGuard &&
      primitiveArgErrorGuard

#eval assignPrimitiveGuard

#guard assignPrimitiveGuard

def runChecks : IO Bool := do
  if assignPrimitiveGuard then
    IO.println "PASS exact panSem Assign/Primitive clauses (8 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem Assign/Primitive clauses"
    pure false

end Flapjack.Test.PanSemAssignPrimitiveExactParity
