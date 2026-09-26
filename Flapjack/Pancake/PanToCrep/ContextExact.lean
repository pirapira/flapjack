import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.PanLang.Decl

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

open Flapjack.Pancake.PanLang (MlS ShapeHOL DeclHOL)

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

open Flapjack.Basis.Pure.MlString

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

/-! Production boundary adapter for callers that still consume
`PanToCrepHOLContext`. This conversion is total from the exact context: HOL
`MlString` keys decode to byte-valued `String`s, `ShapeHOL` payloads decode
through the existing shape codec, and the word-indexed exception codes retain
their width. It is an untagged representation bridge, not a port of a
consumer theorem. It is intentionally one-way for arbitrary production
contexts: their raw function maps carry no finite-support evidence, and
production `String` keys / `Shape` names can contain values outside HOL's byte
range. A reverse bridge needs explicit finite-support, `NameRanged`, and
`ShapeByteRanged` evidence; this adapter does not claim that arbitrary
production contexts round-trip. -/
def toProduction {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    PanToCrepHOLContext (BitVec width) where
  vars := fun name =>
    (context.vars.lookup (ofString name)).map
      fun (shape, names) => (Flapjack.Pancake.PanLang.shapeOfHOL shape, names)
  funcs := fun name =>
    (context.funcs.lookup (ofString name)).map fun (params, resultShape) =>
      (params.map fun (paramName, shape) =>
        (toStringOfBytes paramName, Flapjack.Pancake.PanLang.shapeOfHOL shape),
       Flapjack.Pancake.PanLang.shapeOfHOL resultShape)
  eids := fun name => context.eids.lookup (ofString name)
  vmax := context.vmax

@[simp] theorem toProduction_vars_lookup {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) :
    context.toProduction.vars (toStringOfBytes name) =
      (context.vars.lookup name).map
        fun (shape, names) => (Flapjack.Pancake.PanLang.shapeOfHOL shape, names) := by
  simp [toProduction, ofString_toStringOfBytes]

@[simp] theorem toProduction_funcs_lookup {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) :
    context.toProduction.funcs (toStringOfBytes name) =
      (context.funcs.lookup name).map fun (params, resultShape) =>
        (params.map fun (paramName, shape) =>
          (toStringOfBytes paramName, Flapjack.Pancake.PanLang.shapeOfHOL shape),
         Flapjack.Pancake.PanLang.shapeOfHOL resultShape) := by
  simp [toProduction, ofString_toStringOfBytes]

@[simp] theorem toProduction_eids_lookup {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) :
    context.toProduction.eids (toStringOfBytes name) = context.eids.lookup name := by
  simp [toProduction, ofString_toStringOfBytes]

theorem toProduction_key_nameRanged (name : MlS) :
    Flapjack.Pancake.PanLang.NameRanged (toStringOfBytes name) := by
  intro character hcharacter
  unfold toStringOfBytes at hcharacter
  rw [String.toList_ofList] at hcharacter
  obtain ⟨byte, hbyte, rfl⟩ := List.mem_map.mp hcharacter
  rw [ofNat_toNat_char]
  have hlt := byte.isLt
  simpa using hlt

theorem toProduction_shapeByteRanged : (shape : ShapeHOL) →
    Flapjack.Pancake.PanLang.ShapeByteRanged
      (Flapjack.Pancake.PanLang.shapeOfHOL shape)
  | .one => by
      simp [Flapjack.Pancake.PanLang.shapeOfHOL,
        Flapjack.Pancake.PanLang.ShapeByteRanged]
  | .comb fields => by
      simp only [Flapjack.Pancake.PanLang.shapeOfHOL,
        Flapjack.Pancake.PanLang.ShapeByteRanged]
      intro productionShape hproductionShape
      obtain ⟨shape, hshape, rfl⟩ := List.mem_map.mp hproductionShape
      exact toProduction_shapeByteRanged shape
  | .named name => by
      simpa [Flapjack.Pancake.PanLang.shapeOfHOL,
        Flapjack.Pancake.PanLang.ShapeByteRanged] using
        toProduction_key_nameRanged name

end PanToCrepContextExact

/-- HOL `pan_to_crep$get_eids_from_decls`' association list
    (`pan_to_crepScript.sml:356-364`): the exception names of a declaration list
    paired with their `GENLIST`-indexed word codes (`MAP FST (exceptions decls)`
    zipped with `GENLIST (n2w x) (LENGTH eids)`). Flapjack-only infrastructure
    naming that list; not a separate HOL declaration. -/
def getEidsEntriesHOL {width : Nat} [NeZero width] (decls : List (DeclHOL width)) :
    List (MlS × BitVec width) :=
  let eids := (Flapjack.Pancake.PanLang.exceptionsHOL decls).map Prod.fst
  eids.zip ((List.range eids.length).map (BitVec.ofNat width))

/-- Exact port of HOL `pan_to_crep$get_eids_from_decls`
    (`cakeml/pancake/pan_to_crepScript.sml:356-364`):
    `get_eids_from_decls decls = let eids = MAP FST (exceptions decls);
    ns = GENLIST (λx. (n2w x):'a word) (LENGTH eids); es = MAP2 (λx y. (x,y))
    eids ns in alist_to_fmap es`. The result carrier is the canonical
    finite-support `HolFiniteMapExact MlS (BitVec width)`, whose `lookup` is the
    HOL-shaped right-fold association-list rendering `alistToFmap` (HOL
    `alist_to_fmap`), and HOL `n2w` is `BitVec.ofNat width`. The standalone
    `fmap_as_finite_support_result` qualifier records only that finite-support
    representation; the quantifier, input carrier, and result values match HOL,
    and the same-module witness below states the unconditional lookup-level
    correspondence. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def"
  (fmap_as_finite_support_result)]
def getEidsFromDeclsHOL {width : Nat} [NeZero width] (decls : List (DeclHOL width)) :
    HolFiniteMapExact MlS (BitVec width) where
  lookup := Flapjack.alistToFmap (getEidsEntriesHOL decls)
  finiteSupport := by
    refine ⟨(getEidsEntriesHOL decls).map Prod.fst, ?_⟩
    intro key hkey
    obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hkey
    obtain ⟨entry, hentry, hkeyeq, -⟩ :=
      Flapjack.flookupAlistToFmap_mem (getEidsEntriesHOL decls) key value hvalue
    exact List.mem_map.mpr ⟨entry, hentry, hkeyeq⟩

/-- Canonical standalone finite-map witness for `getEidsFromDeclsHOL`: its
    `lookup` is exactly the HOL-shaped raw association-list map rendering
    `alistToFmap` (HOL `alist_to_fmap`), with no premises and no dependence on
    the canonical `HolFiniteMapExact` wrapper. -/
theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL
    {width : Nat} [NeZero width] (decls : List (DeclHOL width)) (key : MlS) :
    ((getEidsFromDeclsHOL decls : HolFiniteMapExact MlS (BitVec width))).lookup key =
      Flapjack.FLOOKUP (Flapjack.alistToFmap (getEidsEntriesHOL decls)) key := rfl

end Flapjack
