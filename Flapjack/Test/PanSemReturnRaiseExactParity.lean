import Flapjack.Pancake.Semantics.PanSem.ReturnRaiseExact

/-!
# Direct-HOL-row parity for the exact `Return`/`Raise` clause fragments

Reproduces the committed original-HOL rows in
`scripts/hol-probes/pan_sem_e2e_probe.out`:

```
return_clears_locals=(SOME (Return (ValWord 41w)),NONE)
return_shape_too_big=SOME Error
raise_clears_locals=(SOME (Exception «E» (ValWord 5w)),NONE)
raise_missing_exception=SOME Error
raise_shape_mismatch=SOME Error
```

The `HolValue`/`ValueHOL` and `PanSemResultExact` carriers derive only `Repr`,
so the guards project the interesting payload to `Nat`/`Bool` and compare with
`==`.
-/

namespace Flapjack.Test.PanSemReturnRaiseExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL)

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word64 := RiscV.Word 64

/-- An exact state with local `x = 7` and exception shape `E = One`. -/
abbrev baseState : PanSemStateExact 64 Unit :=
  { locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun name => if name = ml "E" then some .one else none
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

/-- A state with no declared exception shapes. -/
abbrev noExceptionState : PanSemStateExact 64 Unit :=
  { baseState with eshapes := fun _ => none }

/-- Fixture expression evaluation: constants, and the empty record. -/
def evalExpressionFixture (_state : PanSemStateExact 64 Unit)
    (expression : ExpHOL 64) : Option (ValueHOL 64) :=
  match expression with
  | .const value => some (.val (.word value))
  | .rstruct [] => some (.rStruct [])
  | _ => none

/-- A return/exception value of 33 `One` fields, whose size exceeds 32. -/
def tooBigValue : ExpHOL 64 :=
  .rstruct (List.replicate 33 (.const 0))

def returnedWord (result : Option (PanSemResultExact 64)) : Option Nat :=
  match result with
  | some (.returned (.val (.word value))) => some value.toNat
  | _ => none

def raisedWord (exceptionId : String)
    (result : Option (PanSemResultExact 64)) : Option Nat :=
  match result with
  | some (.exception name (.val (.word value))) =>
      if name = ml exceptionId then some value.toNat else none
  | _ => none

def isErrorResult (result : Option (PanSemResultExact 64)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def localsWord (state : PanSemStateExact 64 Unit) (name : String) : Option Nat :=
  match state.locals (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def returnClearsLocalsGuard : Bool :=
  let result := returnStepHOLExact baseState (.const 41) evalExpressionFixture
  returnedWord result.1 == some 41 && (localsWord result.2 "x").isNone

def returnShapeTooBigGuard : Bool :=
  let result := returnStepHOLExact baseState tooBigValue evalExpressionFixture
  isErrorResult result.1 && localsWord result.2 "x" == some 7

def raiseClearsLocalsGuard : Bool :=
  let result := raiseStepHOLExact baseState (ml "E") (.const 5) evalExpressionFixture
  raisedWord "E" result.1 == some 5 && (localsWord result.2 "x").isNone

def raiseMissingExceptionGuard : Bool :=
  let result := raiseStepHOLExact noExceptionState (ml "E") (.const 5) evalExpressionFixture
  isErrorResult result.1

def raiseShapeMismatchGuard : Bool :=
  let result := raiseStepHOLExact baseState (ml "E") (.rstruct []) evalExpressionFixture
  isErrorResult result.1

def returnRaiseGuard : Bool :=
  returnClearsLocalsGuard
    && returnShapeTooBigGuard
    && raiseClearsLocalsGuard
    && raiseMissingExceptionGuard
    && raiseShapeMismatchGuard

#guard returnClearsLocalsGuard
#guard returnShapeTooBigGuard
#guard raiseClearsLocalsGuard
#guard raiseMissingExceptionGuard
#guard raiseShapeMismatchGuard
#guard returnRaiseGuard

def runChecks : IO Bool := do
  if returnRaiseGuard then
    IO.println "PASS exact panSem empty_locals/Return/Raise clauses (5 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem empty_locals/Return/Raise clauses"
    pure false

end Flapjack.Test.PanSemReturnRaiseExactParity
