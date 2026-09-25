import Flapjack.Pancake.Semantics.PanSem.DecExact

/-!
# Exact `panSem$empty_locals` and the `Return`/`Raise` evaluation clauses

HOL `empty_locals` (`cakeml/pancake/semantics/panSemScript.sml:398-401`) clears
only the source state's local map:

```
empty_locals s = s with locals := FEMPTY
```

The `Return` and `Raise` clauses of `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:625-630`) are

```
evaluate (Return e, s) =
  case eval s e of
    SOME value =>
      if size_of_sh_with_ctxt s.structs (shape_of value) <= 32
      then (SOME (Return value), empty_locals s) else (SOME Error, s)
  | NONE => (SOME Error, s)

evaluate (Raise eid e, s) =
  case (FLOOKUP s.eshapes eid, eval s e) of
    (SOME sh, SOME value) =>
      if shape_of value = sh /\ size_of_sh_with_ctxt s.structs (shape_of value) <= 32
      then (SOME (Exception eid value), empty_locals s) else (SOME Error, s)
  | _ => (SOME Error, s)
```

The `empty_locals_def`-shaped helper `emptyLocalsHOLExact` over the
`mlstring`-keyed `PanSemStateExact` carrier lives in
`Flapjack/Pancake/Semantics/PanSem/StateExact.lean` and is reused here. That
helper is currently **untagged** because `PanSemStateExact` stores its map fields
as unrestricted lookup functions rather than HOL finite maps (carrier gap tracked
by bead `flapjack-pxn.18.3.7.1.3.1.1.2`).
The two clause steps `returnStepHOLExact` / `raiseStepHOLExact` are
callback-parameterised partial-evaluator infrastructure (the embedded `eval`
is a parameter), so they are deliberately **untagged**: there is no full
HOL-shaped `evaluate` yet and no false `evaluate_def` tag is claimed.  The
fragments reuse the exact helpers `sizeOfShapeWithContextHOL`, `shapeOfHOLExact`
and `shapeEqHOL`.  Direct original-HOL rows are reproduced by
`Flapjack/Test/PanSemReturnRaiseExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- The `Return` clause of HOL `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:625-627`): evaluate the returned
expression, check `size_of_sh_with_ctxt s.structs (shape_of value) <= 32`, and
on success return the value while clearing the locals. -/
def returnStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state expression with
  | some value =>
      if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
          (shapeOfHOLExact value) ≤ 32 then
        (some (.returned value), emptyLocalsHOLExact state)
      else (some .error, state)
  | none => (some .error, state)

/-- The `Raise` clause of HOL `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:628-630`): evaluate the exception
value, require a matching `FLOOKUP s.eshapes eid` and
`shape_of value = sh`, check `size_of_sh_with_ctxt s.structs (shape_of value)
<= 32`, and on success raise while clearing the locals. -/
def raiseStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state expression with
  | some value =>
      match state.eshapes exceptionId with
      | some shape =>
          if shapeEqHOL (shapeOfHOLExact value) shape then
            if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                (shapeOfHOLExact value) ≤ 32 then
              (some (.exception exceptionId value), emptyLocalsHOLExact state)
            else (some .error, state)
          else (some .error, state)
      | none => (some .error, state)
  | none => (some .error, state)

theorem returnStepHOLExact_eval_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : evalExpression state expression = none) :
    returnStepHOLExact state expression evalExpression = (some .error, state) := by
  simp only [returnStepHOLExact, h]

theorem returnStepHOLExact_size_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (h : evalExpression state expression = some value)
    (hsize : ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
      (shapeOfHOLExact value) ≤ 32) :
    returnStepHOLExact state expression evalExpression = (some .error, state) := by
  simp [returnStepHOLExact, h, hsize]

theorem returnStepHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (h : evalExpression state expression = some value)
    (hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
      (shapeOfHOLExact value) ≤ 32) :
    returnStepHOLExact state expression evalExpression =
      (some (.returned value), emptyLocalsHOLExact state) := by
  simp [returnStepHOLExact, h, hsize]

theorem raiseStepHOLExact_eval_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : evalExpression state expression = none) :
    raiseStepHOLExact state exceptionId expression evalExpression = (some .error, state) := by
  simp only [raiseStepHOLExact, h]

theorem raiseStepHOLExact_missing {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (h : evalExpression state expression = some value)
    (hmissing : state.eshapes exceptionId = none) :
    raiseStepHOLExact state exceptionId expression evalExpression = (some .error, state) := by
  simp [raiseStepHOLExact, h, hmissing]

theorem raiseStepHOLExact_shape_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (shape : Flapjack.Pancake.PanLang.ShapeHOL)
    (h : evalExpression state expression = some value)
    (hshape : state.eshapes exceptionId = some shape)
    (hmismatch : shapeEqHOL (shapeOfHOLExact value) shape = false) :
    raiseStepHOLExact state exceptionId expression evalExpression = (some .error, state) := by
  simp [raiseStepHOLExact, h, hshape, hmismatch]

theorem raiseStepHOLExact_size_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (shape : Flapjack.Pancake.PanLang.ShapeHOL)
    (h : evalExpression state expression = some value)
    (hshape : state.eshapes exceptionId = some shape)
    (hmatch : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (hsize : ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
      (shapeOfHOLExact value) ≤ 32) :
    raiseStepHOLExact state exceptionId expression evalExpression = (some .error, state) := by
  simp [raiseStepHOLExact, h, hshape, hmatch, hsize]

theorem raiseStepHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (value : ValueHOL width) (shape : Flapjack.Pancake.PanLang.ShapeHOL)
    (h : evalExpression state expression = some value)
    (hshape : state.eshapes exceptionId = some shape)
    (hmatch : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
      (shapeOfHOLExact value) ≤ 32) :
    raiseStepHOLExact state exceptionId expression evalExpression =
      (some (.exception exceptionId value), emptyLocalsHOLExact state) := by
  simp [raiseStepHOLExact, h, hshape, hmatch, hsize]

end Flapjack
