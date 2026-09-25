/-
  Function-backed `panSem$lookup_code` and callback-parameterised DecCall
  clause over the `mlstring`-keyed source state. `PanSemStateExact.code` and the
  helper's `code` parameter are unrestricted functions rather than HOL finite
  maps, so `lookupCodeHOLExact` is untagged.

  `lookup_code_def` (cakeml/pancake/semantics/panSemScript.sml:458-467) looks the
  function name up in the state's code finite map and checks that the formal
  parameter list has no duplicate names (`ALL_DISTINCT (MAP FST vshapes)`) and
  that each formal's shape matches the corresponding argument's `shape_of`
  (`LIST_REL (λ vshape arg. SND vshape = shape_of arg) vshapes args`); on success
  it returns the body, the locals map `FEMPTY |++ ZIP (MAP FST vshapes,args)`,
  and the declared return shape. The Lean rendering uses `MlS` funname keys and
  `ValueHOL` arguments, and renders `LIST_REL` as length equality plus a zipped
  pointwise `shapeEqHOL` (whose `= true` bridge is
  `shapeEqHOL_eq_true`), and folds the `=`-keyed function update left to right.

  The DecCall clause (panSemScript.sml:693-718) evaluates the argument
  expressions, looks the function up, and on a positive clock runs the body on
  `dec_clock s with locals := newlocals` under `fix_clock`; `NONE`/`Break`/
  `Continue` become `Error`, a `Return retv` whose `shape_of` matches both the
  clause shape and the declared return shape runs the continuation under
  `set_var rt retv` and restores the caller's previous `rt` binding with
  `res_var`, and any other result clears the locals.  That clause step is
  callback-parameterised (the recursive `evaluate` call is supplied by the
  caller) and is therefore deliberately untagged: only the whole recursive
  `evaluate_def` statement can carry a `@[hol]` tag.
-/
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- Function-backed rendering of HOL `panSem$lookup_code` (`panSemScript.sml:458-467`).
    The lookup and argument checks are retained, but this helper is untagged
    because `code` is an unrestricted function rather than a HOL finite map.
    Exact finite-support replacement tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
def lookupCodeHOLExact {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (arguments : List (ValueHOL width)) :
    Option (ProgHOL width × (MlS → Option (ValueHOL width)) × ShapeHOL) :=
  match code fname with
  | none => none
  | some (parameters, body, returnShape) =>
      if (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true then
        some (body,
          List.foldl
            (fun (map : MlS → Option (ValueHOL width)) (entry : MlS × ValueHOL width) =>
              fun current => if current = entry.1 then some entry.2 else map current)
            (fun _ => none) ((parameters.map Prod.fst).zip arguments),
          returnShape)
      else none

@[simp] theorem lookupCodeHOLExact_of_code_none {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (arguments : List (ValueHOL width))
    (h : code fname = none) :
    lookupCodeHOLExact code fname arguments = none := by
  simp [lookupCodeHOLExact, h]

/-- Untagged callback-parameterised step for the HOL `evaluate` DecCall clause
    (`panSemScript.sml:693-718`) over the exact `mlstring`-keyed state.  The
    recursive `evaluate` call is supplied by the caller so this remains an
    untagged clause step rather than a second evaluator. -/
def decCallStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (fname : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
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
                if (shapeEqHOL (shapeOfHOLExact value) shape &&
                    shapeEqHOL (shapeOfHOLExact value) returnShape) then
                  let after : PanSemStateExact width σ :=
                    { result.2 with locals := state.locals }
                  let final :=
                    evaluate continuation (setVarHOLExact resultName value after)
                  (final.1, { final.2 with
                    locals := resVarHOLExact final.2.locals (resultName, state.locals resultName) })
                else (some .error, result.2)
            | some other => (other, emptyLocalsHOLExact result.2)

@[simp] theorem decCallStepHOLExact_eval_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (resultName : MlS) (shape : ShapeHOL)
    (fname : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalExpressions state arguments = none) :
    decCallStepHOLExact state resultName shape fname arguments continuation
      evalExpressions evaluate = (some .error, state) := by
  simp [decCallStepHOLExact, h]

theorem decCallStepHOLExact_lookup_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (resultName : MlS) (shape : ShapeHOL)
    (fname : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (values : List (ValueHOL width))
    (hargs : evalExpressions state arguments = some values)
    (hlookup : lookupCodeHOLExact state.code fname values = none) :
    decCallStepHOLExact state resultName shape fname arguments continuation
      evalExpressions evaluate = (some .error, state) := by
  simp [decCallStepHOLExact, hargs, hlookup]

theorem decCallStepHOLExact_timeout {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (resultName : MlS) (shape : ShapeHOL)
    (fname : MlS) (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
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
    decCallStepHOLExact state resultName shape fname arguments continuation
      evalExpressions evaluate = (some .timeOut, emptyLocalsHOLExact state) := by
  simp [decCallStepHOLExact, hargs, hlookup, hclock]

/-! ## Exact `LIST_REL` carrier and the `vshapes`/`args` length/MAP lemma

HOL `panSemScript.sml:740` states `vshapes_args_rel_imp_eq_len_MAP` for the
exact `LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args`
relation used by `lookup_code`.  This Lean core does not provide
`List.Forall₂` (see `Flapjack/FfiBridge.lean`), so the exact carrier is the
propositional `ListRel` below. -/

/-- Exact Lean rendering of HOL `LIST_REL`: pointwise relation with matching
    list structure.  Untagged Flapjack infrastructure (the core here has no
    `List.Forall₂`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

/-- Exact port of HOL `panSem$vshapes_args_rel_imp_eq_len_MAP`
    (`panSemScript.sml:740`): the shape relation between declared parameters
    and evaluated arguments implies both the length and the `MAP SND`/`MAP
    shape_of` equalities. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "vshapes_args_rel_imp_eq_len_MAP"]
theorem vshapesArgsRel_imp_eq_len_MAP {width : Nat} [NeZero width]
    (vshapes : List (MlS × ShapeHOL)) (args : List (ValueHOL width))
    (h : ListRel (fun vshape arg => vshape.2 = shapeOfHOLExact arg) vshapes args) :
    vshapes.length = args.length ∧
      vshapes.map Prod.snd = args.map shapeOfHOLExact := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd _ ih => exact ⟨by simpa using ih.1, by simp [hd, ih.2]⟩

end Flapjack
