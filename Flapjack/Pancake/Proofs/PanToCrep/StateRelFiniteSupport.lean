import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Finite-support Pan-to-Crep relation infrastructure for the shape-invariant
proof path. The field types follow HOL `state_rel_def` and `locals_rel_def`:
`MlS`, `ValueHOL`, `ShapeHOL`, finite-support maps, and `CrepSemHOLState`.

These declarations are intentionally untagged support. The current
`fmap_as_finite_support` qualifier can certify fields owned by one carrier
structure, while these relations span the separate PanSem and CrepSem state
carriers. They are not claims that a HOL relation declaration has been
ported; the exact theorem tag must wait for reviewed multi-carrier qualifier
support and the faithful evaluator proof.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL StructContextExact isWfShapeExactHOL)

/-- Flapjack-specific exact-map bound predicate for relation support. It
    mirrors the shape of HOL `ctxt_max_def`, but is not a tagged port: it takes
    a bare finite-map parameter without the owning carrier witness required by
    the current finite-map qualifier. -/
def ctxtMaxFiniteExact {κ β : Type}
    (n : Nat) (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ key shape slots, map.lookup key = some (shape, slots) →
    ∀ slot ∈ slots, slot ≤ n

/-- Flapjack-specific exact-map overlap predicate for relation support. It
    mirrors the shape of HOL `no_overlap_def`, but is not a tagged port because
    its bare map parameter cannot carry the reviewed finite-map qualifier. -/
def noOverlapFiniteExact {κ β : Type}
    (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  (∀ key shape slots, map.lookup key = some (shape, slots) → slots.Nodup) ∧
    ∀ key key' shape shape' slots slots',
      map.lookup key = some (shape, slots) →
      map.lookup key' = some (shape', slots') →
      (∃ slot, slot ∈ slots ∧ slot ∈ slots') → key = key'

/-- Flapjack-specific state-relation support over the exact finite-support
    PanSem and CrepSem carriers. `globals.lookup = none` renders HOL `FEMPTY`;
    this is not a tagged `state_rel_def` port because its finite-map fields span
    two owning state carriers. -/
def panToCrepStateRelFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ) : Prop :=
  source.memory = target.memory ∧
    source.memaddrs = target.memaddrs ∧
    source.shMemaddrs = target.shMemaddrs ∧
    source.structs = [] ∧
    source.globals.lookup = (fun _ => none) ∧
    source.clock = target.clock ∧
    source.be = target.be ∧
    source.ffi = target.ffi ∧
    source.baseAddr = target.baseAddr ∧
    source.topAddr = target.topAddr

/-- Flapjack-specific local-relation support over the exact finite-support
    PanSem value and CrepSem word carriers. The final conjunct preserves the
    source shape invariant; this is not a tagged `locals_rel_def` port because
    the relation spans separate map carriers. -/
def panToCrepLocalsRelFiniteExact {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width)) : Prop :=
  noOverlapFiniteExact context.vars ∧
    ctxtMaxFiniteExact context.vmax context.vars ∧
    ∀ name value, sourceLocals.lookup name = some value →
      ∃ slots words,
        context.vars.lookup name = some (shapeOfHOLExact value, slots) ∧
        slots.mapM targetLocals.lookup = some words ∧
        flattenHOL value = words ∧
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true

/-- The exact finite-support locals relation immediately supplies the
    `is_wf_shape_v_nil` fact for every present source local, matching HOL's
    `locals_rel_wf_shape` proof. -/
theorem panToCrepLocalsRelFiniteExact_shapeProjection {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  obtain ⟨slots, words, _hcontext, _hmapped, _hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  exact hwf

/-- The value-level well-formedness fact is a separate bridge from the literal
    HOL `locals_rel` conjunct `is_wf_shape_nil (shape_of v)`. -/
theorem panToCrepLocalsRelFiniteExact_valueShapeProjection {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    isWfShapeValueHOLExact [] value = true := by
  have hshape := panToCrepLocalsRelFiniteExact_shapeProjection
    context sourceLocals targetLocals name value hrel hlookup
  have hbridge := isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil
    ([] : StructContextExact) rfl value
  rw [hbridge] at hshape
  exact hshape

/-- Projection of HOL `state_rel_def`'s structural-context conjunct. -/
theorem panToCrepStateRelFiniteExact_structs {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.structs = [] := hrel.2.2.2.1

end Flapjack
