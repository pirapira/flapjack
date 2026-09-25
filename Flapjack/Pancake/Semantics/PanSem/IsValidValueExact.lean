/-
  Function-backed rendering of HOL `panSem$is_valid_value`. Its source state
  has unrestricted lookup functions, not HOL finite-map fields; the declaration
  is kept untagged for that carrier mismatch.

  HOL reference: `cakeml/pancake/semantics/panSemScript.sml:469-475`:

  ```
  Definition is_valid_value_def:
    is_valid_value s vk v value =
    case lookup_kvar vk v s of
       | SOME w => shape_of value = shape_of w
       | NONE => F
  ```

  The comparison `shape_of value = shape_of w` is rendered with the untagged
  executable `shapeEqHOL`, whose truth is proved equivalent to HOL equality on
  the exact `ShapeHOL` carrier (`shapeEqHOL_eq_true`).  The exact datatypes
  derive only `Repr`, so a `Bool` structural equality is supplied here rather
  than relying on `DecidableEq`; the bridge theorem records that this changes
  nothing about the statement.

  Direct original-HOL rows: `scripts/hol-probes/pan_sem_is_valid_value_probe.out`
  (`is_valid_value_local_shape=T`, `is_valid_value_global_shape=T`,
  `is_valid_value_mismatch=F`, `is_valid_value_missing=F`) and
  `scripts/hol-probes/pan_is_valid_value_probe.out`.
-/
import Flapjack.Pancake.Semantics.PanSem.StateExact

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL)

/-- Executable structural equality on the exact `ShapeHOL` carrier.  Untagged:
HOL compares shapes with `=`; this `Bool` rendering agrees with that equality
by `shapeEqHOL_eq_true`. -/
def shapeEqHOL : ShapeHOL → ShapeHOL → Bool
  | .one, .one => true
  | .named left, .named right => decide (left = right)
  | .comb left, .comb right => shapeEqListHOL left right
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
where
  shapeEqListHOL : List ShapeHOL → List ShapeHOL → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        shapeEqHOL left right && shapeEqListHOL leftRest rightRest
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right
    decreasing_by
      all_goals first | decreasing_trivial

/- Truth of `shapeEqHOL` is exactly HOL structural equality on shapes. -/
mutual
  theorem shapeEqHOL_eq_true : (left right : ShapeHOL) →
      (shapeEqHOL left right = true ↔ left = right)
    | .one, .one => by simp only [shapeEqHOL]
    | .named left, .named right => by
        simp only [shapeEqHOL, ShapeHOL.named.injEq, decide_eq_true_eq]
    | .comb left, .comb right => by
        simp only [shapeEqHOL, ShapeHOL.comb.injEq]
        exact shapeEqListHOL_eq_true left right
    | .one, .named _ => by simp [shapeEqHOL]
    | .one, .comb _ => by simp [shapeEqHOL]
    | .named _, .one => by simp [shapeEqHOL]
    | .named _, .comb _ => by simp [shapeEqHOL]
    | .comb _, .one => by simp [shapeEqHOL]
    | .comb _, .named _ => by simp [shapeEqHOL]

  theorem shapeEqListHOL_eq_true : (left right : List ShapeHOL) →
      (shapeEqHOL.shapeEqListHOL left right = true ↔ left = right)
    | [], [] => by simp only [shapeEqHOL.shapeEqListHOL]
    | left :: leftRest, right :: rightRest => by
        simp only [shapeEqHOL.shapeEqListHOL, Bool.and_eq_true]
        rw [shapeEqHOL_eq_true left right,
          shapeEqListHOL_eq_true leftRest rightRest]
        exact ⟨fun h => (List.cons.injEq ..).mpr h, fun h => (List.cons.injEq ..).mp h⟩
    | [], _ :: _ => by simp [shapeEqHOL.shapeEqListHOL]
    | _ :: _, [] => by simp [shapeEqHOL.shapeEqListHOL]
end

/-- Function-backed rendering of HOL `is_valid_value` (`panSemScript.sml:469-475`).
    Kept untagged because its `PanSemStateExact` argument admits arbitrary
    lookup functions rather than HOL finite-map fields. Exact finite-support
    replacement tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
def isValidValueHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) : Bool :=
  match lookupKvarHOLExact kind name state with
  | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
  | none => false

end Flapjack
