import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact

/-!
# Exact HOL `panSem$result` carrier and the `Dec`-with-initializer clause

HOL `panSemScript.sml:68-75` declares

```
Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a v)
         | Exception mlstring ('a v)
         | FinalFFI final_event
End
```

and `evaluate_def` (`panSemScript.sml:555-565`) evaluates a `Dec` with an
initializer expression by

```
evaluate (Dec v sh e prog, s) =
  case eval s e of
   | SOME value =>
      if sh = shape_of value then
        let (res,st) = evaluate (prog, s with locals := s.locals |+ (v,value)) in
        (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
      else (SOME Error, s)
   | NONE => (SOME Error, s)
```

`PanSemResultExact` below is the exact `result` carrier over the faithful
`ValueHOL`/`HolFinalEvent` payloads (`Flapjack.Pancake.Semantics.PanSem.ValueHOL`)
and is tagged against `result`.

`decStepHOLExact` is the `Dec` clause as a step over the exact
`PanSemStateExact` state. It is parameterised by an initializer evaluator and a
body evaluator (callbacks), because the recursive source evaluator over the
exact carrier is not assembled yet; therefore the clause itself is
FLAPJACK-SPECIFIC infrastructure and carries NO `@[hol]` tag. It uses only
exact helpers: `shapeOfHOLExact`, the `shapeEqHOL` equality rendering (with its
proved `shapeEqHOL_eq_true` bridge), `setVarHOLExact`, and `resVarHOLExact`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- Exact `panSem$result` (`panSemScript.sml:68-75`): seven constructors whose
    `returned`/`exception` payloads are the exact `ValueHOL` carrier and whose
    `finalFfi` carries the exact `HolFinalEvent`; `Exception` stores the
    `mlstring` exception identifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "result"]
inductive PanSemResultExact (width : Nat) [NeZero width] where
  | error
  | timeOut
  | break
  | continue
  | returned (value : ValueHOL width)
  | exception (exceptionId : MlS) (value : ValueHOL width)
  | finalFfi (event : HolFinalEvent)
  deriving Repr

/-- HOL `Dec`-with-initializer clause (`panSemScript.sml:555-565`) over the
    exact state.  The initializer is evaluated by `evalInitializer`; on success
    the declared shape must equal `shape_of` the value, the body runs with the
    local binding installed (`setVarHOLExact .local`), and afterwards the
    previous binding of the name is restored with `resVarHOLExact` exactly as
    HOL's `res_var st.locals (v, FLOOKUP s.locals v)`.  Untagged because the
    evaluator callbacks are supplied by the caller. -/
def decStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (evalInitializer : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluateBody : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalInitializer state initializer with
  | some value =>
      if shapeEqHOL shape (shapeOfHOLExact value) then
        let result := evaluateBody body (setVarHOLExact name value state)
        (result.1, { result.2 with
          locals := resVarHOLExact result.2.locals (name, state.locals name) })
      else (some .error, state)
  | none => (some .error, state)

/-- The initializer-evaluation failure branch returns `SOME Error` and leaves
    the state unchanged. -/
theorem decStepHOLExact_initializer_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (evalInitializer : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluateBody : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalInitializer state initializer = none) :
    decStepHOLExact state name shape initializer body evalInitializer evaluateBody
      = (some .error, state) := by
  simp only [decStepHOLExact, h]

/-- The shape-mismatch branch returns `SOME Error` and leaves the state
    unchanged. -/
theorem decStepHOLExact_shape_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (evalInitializer : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluateBody : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (value : ValueHOL width) (h : evalInitializer state initializer = some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = false) :
    decStepHOLExact state name shape initializer body evalInitializer evaluateBody
      = (some .error, state) := by
  simp [decStepHOLExact, h, hshape]

/-- The success branch installs the binding, runs the body, and restores the
    previous local binding. -/
theorem decStepHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (evalInitializer : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluateBody : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (value : ValueHOL width) (h : evalInitializer state initializer = some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = true) :
    decStepHOLExact state name shape initializer body evalInitializer evaluateBody
      = (let result := evaluateBody body (setVarHOLExact name value state)
         (result.1, { result.2 with
           locals := resVarHOLExact result.2.locals (name, state.locals name) })) := by
  simp [decStepHOLExact, h, hshape]

end Flapjack
