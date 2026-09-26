import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.PanLang.Prog

/-!
Production-to-exact context correspondence under the invariants the production
carrier does not encode. The production `FiniteMap` is an unrestricted function,
so this bridge requires finite-support evidence. String-backed keys and shape
names must also be byte-ranged before they can be represented without loss by
HOL `mlstring`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL NameRanged ShapeByteRanged shapeToHOL shapeOfHOL)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

/-- The support and byte-range evidence needed to encode a production context
    as the exact HOL finite-map carrier. These invariants are explicit because
    `PanToCrepHOLContext` itself does not enforce any of them. -/
structure PanToCrepContextProductionEvidence {width : Nat}
    (context : PanToCrepHOLContext (BitVec width)) : Prop where
  varsSupport : ∃ keys : List String, ∀ key, context.vars key ≠ none → key ∈ keys
  funcsSupport : ∃ keys : List String, ∀ key, context.funcs key ≠ none → key ∈ keys
  eidsSupport : ∃ keys : List String, ∀ key, context.eids key ≠ none → key ∈ keys
  varsRanged : ∀ key value, context.vars key = some value →
    NameRanged key ∧ ShapeByteRanged value.1
  funcsRanged : ∀ key value, context.funcs key = some value →
    NameRanged key ∧
      (∀ parameter ∈ value.1, NameRanged parameter.1 ∧ ShapeByteRanged parameter.2) ∧
      ShapeByteRanged value.2
  eidsRanged : ∀ key value, context.eids key = some value → NameRanged key

private def varsExact (context : PanToCrepHOLContext (BitVec width))
    (support : ∃ keys : List String, ∀ key, context.vars key ≠ none → key ∈ keys) :
    HolFiniteMapExact MlS (ShapeHOL × List Nat) where
  lookup key := (context.vars (toStringOfBytes key)).map
    (fun value => (shapeToHOL value.1, value.2))
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := support
    refine ⟨keys.map ofString, ?_⟩
    intro key hlookup
    cases hsource : context.vars (toStringOfBytes key) with
    | none => simp [hsource] at hlookup
    | some value =>
      have hmem := hkeys (toStringOfBytes key) (by simp [hsource])
      have hdecode : ofString (toStringOfBytes key) = key :=
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes key
      exact List.mem_map.mpr ⟨toStringOfBytes key, hmem, hdecode⟩

private def funcsExact (context : PanToCrepHOLContext (BitVec width))
    (support : ∃ keys : List String, ∀ key, context.funcs key ≠ none → key ∈ keys) :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL) where
  lookup key := (context.funcs (toStringOfBytes key)).map fun value =>
    (value.1.map (fun parameter => (ofString parameter.1, shapeToHOL parameter.2)),
      shapeToHOL value.2)
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := support
    refine ⟨keys.map ofString, ?_⟩
    intro key hlookup
    cases hsource : context.funcs (toStringOfBytes key) with
    | none => simp [hsource] at hlookup
    | some value =>
      have hmem := hkeys (toStringOfBytes key) (by simp [hsource])
      have hdecode : ofString (toStringOfBytes key) = key :=
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes key
      exact List.mem_map.mpr ⟨toStringOfBytes key, hmem, hdecode⟩

private def eidsExact (context : PanToCrepHOLContext (BitVec width))
    (support : ∃ keys : List String, ∀ key, context.eids key ≠ none → key ∈ keys) :
    HolFiniteMapExact MlS (BitVec width) where
  lookup key := context.eids (toStringOfBytes key)
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := support
    refine ⟨keys.map ofString, ?_⟩
    intro key hlookup
    have hmem := hkeys (toStringOfBytes key) hlookup
    have hdecode : ofString (toStringOfBytes key) = key :=
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes key
    exact List.mem_map.mpr ⟨toStringOfBytes key, hmem, hdecode⟩

/-- Convert a production context to the exact carrier only when its maps have
    finite support and every key/name that crosses back to String is byte-ranged.
    This is intentionally not a total conversion from arbitrary production
    `PanToCrepHOLContext` values. -/
def panToCrepContextExactOfProduction {width : Nat} [NeZero width]
    (context : PanToCrepHOLContext (BitVec width))
    (_evidence : PanToCrepContextProductionEvidence context) :
    PanToCrepContextExact width where
  vars := varsExact context _evidence.varsSupport
  funcs := funcsExact context _evidence.funcsSupport
  eids := eidsExact context _evidence.eidsSupport
  vmax := context.vmax

@[simp] theorem panToCrepContextExactOfProduction_vars_lookup
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : MlS) :
    (panToCrepContextExactOfProduction context evidence).vars.lookup key =
      (context.vars (toStringOfBytes key)).map
        (fun value => (shapeToHOL value.1, value.2)) := rfl

@[simp] theorem panToCrepContextExactOfProduction_funcs_lookup
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : MlS) :
    (panToCrepContextExactOfProduction context evidence).funcs.lookup key =
      (context.funcs (toStringOfBytes key)).map (fun value =>
        (value.1.map (fun parameter => (ofString parameter.1, shapeToHOL parameter.2)),
          shapeToHOL value.2)) := rfl

@[simp] theorem panToCrepContextExactOfProduction_eids_lookup
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : MlS) :
    (panToCrepContextExactOfProduction context evidence).eids.lookup key =
      context.eids (toStringOfBytes key) := rfl

theorem panToCrepContextExactOfProduction_vars_lookup_roundtrip
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : String)
    (hkey : NameRanged key) :
    ((panToCrepContextExactOfProduction context evidence).vars.lookup (ofString key)).map
      (fun value => (shapeOfHOL value.1, value.2)) = context.vars key := by
  cases hlookup : context.vars key with
  | none =>
    simp [panToCrepContextExactOfProduction_vars_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey, hlookup]
  | some value =>
    have hrange := evidence.varsRanged key value hlookup
    simp [panToCrepContextExactOfProduction_vars_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hrange.1,
      hlookup, Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL, hrange.2]

theorem panToCrepContextExactOfProduction_funcs_lookup_roundtrip
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : String)
    (hkey : NameRanged key) :
    ((panToCrepContextExactOfProduction context evidence).funcs.lookup (ofString key)).map
      (fun value => (value.1.map (fun parameter =>
        (toStringOfBytes parameter.1, shapeOfHOL parameter.2)), shapeOfHOL value.2)) =
      context.funcs key := by
  cases hlookup : context.funcs key with
  | none =>
    simp [panToCrepContextExactOfProduction_funcs_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey, hlookup]
  | some value =>
    have hrange := evidence.funcsRanged key value hlookup
    have hparams := hrange.2.1
    have hparamsMap :
        (value.1.map (fun parameter => (ofString parameter.1,
          shapeToHOL parameter.2))).map (fun parameter =>
            (toStringOfBytes parameter.1, shapeOfHOL parameter.2)) =
          List.map id value.1 := by
      rw [List.map_map]
      apply List.map_congr_left
      intro parameter hparameter
      rcases hparams parameter hparameter with ⟨hname, hshape⟩
      simp [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        parameter.1 hname, Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL,
        hshape]
    simp only [panToCrepContextExactOfProduction_funcs_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey,
      hlookup, Option.map_some]
    simp only [Option.some.injEq]
    apply Prod.ext
    · simpa only [List.map_id] using hparamsMap
    · exact Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL value.2 hrange.2.2

theorem panToCrepContextExactOfProduction_eids_lookup_roundtrip
    {width : Nat} [NeZero width] (context : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence context) (key : String)
    (hkey : NameRanged key) :
    (panToCrepContextExactOfProduction context evidence).eids.lookup (ofString key) =
      context.eids key := by
  cases hlookup : context.eids key with
  | none =>
    simp [panToCrepContextExactOfProduction_eids_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey, hlookup]
  | some value =>
    simp [panToCrepContextExactOfProduction_eids_lookup,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey,
      hlookup]

end Flapjack
