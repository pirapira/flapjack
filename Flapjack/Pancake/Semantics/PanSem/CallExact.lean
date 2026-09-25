/-
  Exact HOL-shaped `panSem$evaluate` Call clause over the exact `mlstring`-keyed
  source state.

  The HOL Call clause (cakeml/pancake/semantics/panSemScript.sml:658-697)
  evaluates the argument expressions, looks the function up with
  `lookup_code`, and on a positive clock runs the body on
  `(dec_clock s) with locals := newlocals` under `fix_clock`.  `NONE`/`Break`/
  `Continue` become `Error`, a `Return retv` whose `shape_of` matches the
  declared return shape is dispatched on `caltyp`: `NONE` returns the value
  after `empty_locals`, `SOME (NONE, _)` keeps the caller's locals, and
  `SOME (SOME (rk, rt), _)` checks `is_valid_value s rk rt retv` and then
  `set_kvar rk rt retv` on the state with the caller's locals.  An
  `Exception eid exn` is dispatched on `caltyp` as well: `NONE` and
  `SOME (_, NONE)` clear the locals and return the exception, while
  `SOME (_, SOME (eid', evar, p))` runs the handler `p` with `evar` bound to
  `exn` when `eid = eid'`, the handler shape from `s.eshapes eid` matches
  `shape_of exn`, and `is_valid_value s Local evar exn` holds.  Any other
  result clears the locals.

  This clause step is callback-parameterised (the recursive `evaluate` call is
  supplied by the caller) and is therefore deliberately untagged: only the
  whole recursive `evaluate_def` statement can carry a `@[hol]` tag.
-/
import Flapjack.Pancake.Semantics.PanSem.DecCallExact

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- Untagged callback-parameterised step for the HOL `evaluate` Call clause
    (`panSemScript.sml:658-697`) over the exact `mlstring`-keyed state.  The
    recursive `evaluate` call is supplied by the caller so this remains an
    untagged clause step rather than a second evaluator. -/
def callStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpressions state arguments with
  | none => (some .error, state)
  | some values =>
      match lookupCodeHOLExact state.code fname values with
      | none => (some .error, state)
      | some (body, calleeLocals, returnShape) =>
          if state.clock = 0 then
            (some .timeOut, emptyLocalsHOLExact state)
          else
            let entry : PanSemStateExact width σ :=
              { state with clock := state.clock - 1, locals := calleeLocals }
            let result := fixClockHOLExact entry (evaluate body entry)
            match result.1 with
            | none => (some .error, result.2)
            | some .break => (some .error, result.2)
            | some .continue => (some .error, result.2)
            | some (.returned value) =>
                if shapeEqHOL (shapeOfHOLExact value) returnShape then
                  match info with
                  | none =>
                      (some (.returned value), emptyLocalsHOLExact result.2)
                  | some (none, _) =>
                      (none, { result.2 with locals := state.locals })
                  | some (some (kind, name), _) =>
                      if isValidValueHOLExact state kind name value then
                        (none, setKvarHOLExact kind name value
                          { result.2 with locals := state.locals })
                      else (some .error, result.2)
                else (some .error, result.2)
            | some (.exception exceptionId exceptionValue) =>
                match info with
                | none =>
                    (some (.exception exceptionId exceptionValue),
                      emptyLocalsHOLExact result.2)
                | some (_, none) =>
                    (some (.exception exceptionId exceptionValue),
                      emptyLocalsHOLExact result.2)
                | some (_, some (handlerId, handlerVar, handlerBody)) =>
                    if exceptionId = handlerId then
                      match state.eshapes exceptionId with
                      | none => (some .error, result.2)
                      | some handlerShape =>
                          if (shapeEqHOL (shapeOfHOLExact exceptionValue) handlerShape &&
                              isValidValueHOLExact state .local handlerVar exceptionValue) then
                            evaluate handlerBody (setVarHOLExact handlerVar exceptionValue
                              { result.2 with locals := state.locals })
                          else (some .error, result.2)
                    else (some (.exception exceptionId exceptionValue),
                      emptyLocalsHOLExact result.2)
            | some other => (other, emptyLocalsHOLExact result.2)

@[simp] theorem callStepHOLExact_eval_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalExpressions state arguments = none) :
    callStepHOLExact state info fname arguments evalExpressions evaluate =
      (some .error, state) := by
  simp [callStepHOLExact, h]

theorem callStepHOLExact_lookup_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (values : List (ValueHOL width))
    (hargs : evalExpressions state arguments = some values)
    (hlookup : lookupCodeHOLExact state.code fname values = none) :
    callStepHOLExact state info fname arguments evalExpressions evaluate =
      (some .error, state) := by
  simp [callStepHOLExact, hargs, hlookup]

theorem callStepHOLExact_timeout {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (values : List (ValueHOL width))
    (body : ProgHOL width) (calleeLocals : MlS → Option (ValueHOL width))
    (returnShape : ShapeHOL)
    (hargs : evalExpressions state arguments = some values)
    (hlookup : lookupCodeHOLExact state.code fname values =
      some (body, calleeLocals, returnShape))
    (hclock : state.clock = 0) :
    callStepHOLExact state info fname arguments evalExpressions evaluate =
      (some .timeOut, emptyLocalsHOLExact state) := by
  simp [callStepHOLExact, hargs, hlookup, hclock]

end Flapjack
