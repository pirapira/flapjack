import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
The exact finite-map carrier for `pan_to_crep$context`.

HOL (`cakeml/pancake/pan_to_crepScript.sml:10-16`) stores three finite maps:
variables to `(shape, word names)`, functions to `(parameter-shapes, result
shape)`, and exception identifiers to words, plus `vmax`. The exact carrier
uses the exact `MlS` and `ShapeHOL` carriers and `BitVec width` for the HOL word
index. `HolFiniteMapExact` is the canonical finite-support translation of each
HOL `fmap`; the field qualifier is justified by the roundtrip witness below.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL)

/-- Broad function-backed representation paired with support evidence, used
    only to state the finite-support representation roundtrip. -/
structure PanToCrepContextBroad (width : Nat) where
  varsLookup : MlS → Option (ShapeHOL × List Nat)
  varsFiniteSupport : ∃ keys : List MlS, ∀ key, varsLookup key ≠ none → key ∈ keys
  funcsLookup : MlS → Option (List (MlS × ShapeHOL) × ShapeHOL)
  funcsFiniteSupport : ∃ keys : List MlS, ∀ key, funcsLookup key ≠ none → key ∈ keys
  eidsLookup : MlS → Option (BitVec width)
  eidsFiniteSupport : ∃ keys : List MlS, ∀ key, eidsLookup key ≠ none → key ∈ keys
  vmax : Nat

/-- Exact HOL `context` record (`pan_to_crepScript.sml:10-16`). Its map fields
    use the reviewed `HolFiniteMapExact` translation of HOL finite maps; source
    keys and shape payloads use `MlS` and `ShapeHOL`, and exception codes are
    words of the context's positive width. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "context"
  (fmap_as_finite_support := [vars, funcs, eids])]
structure PanToCrepContextExact (width : Nat) [NeZero width] where
  vars : HolFiniteMapExact MlS (ShapeHOL × List Nat)
  funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL)
  eids : HolFiniteMapExact MlS (BitVec width)
  vmax : Nat

namespace PanToCrepContextExact

/-- Forget the finite-map wrappers while retaining their finite-support
    witnesses. -/
def toBroad {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextBroad width where
  varsLookup := context.vars.lookup
  varsFiniteSupport := context.vars.finiteSupport
  funcsLookup := context.funcs.lookup
  funcsFiniteSupport := context.funcs.finiteSupport
  eidsLookup := context.eids.lookup
  eidsFiniteSupport := context.eids.finiteSupport
  vmax := context.vmax

/-- Reconstruct the canonical finite-support carrier from its broad record. -/
def ofBroad {width : Nat} [NeZero width] (context : PanToCrepContextBroad width) :
    PanToCrepContextExact width where
  vars := ⟨context.varsLookup, context.varsFiniteSupport⟩
  funcs := ⟨context.funcsLookup, context.funcsFiniteSupport⟩
  eids := ⟨context.eidsLookup, context.eidsFiniteSupport⟩
  vmax := context.vmax

/-- Canonical finite-support witness required by the `context` qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    ofBroad (toBroad context) = context := by
  cases context
  rfl

end PanToCrepContextExact

end Flapjack
