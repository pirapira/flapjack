import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
The exact finite-map carrier for `pan_to_crep$exp_hdl`.

`expHdlHOL` in `Flapjack/Pancake/PanToCrep.lean` takes the production raw
function `MlString -> Option (ShapeHOL × List Nat)`, whose quantified domain is
strictly broader than the HOL finite map `varname |-> (shape # num list)`; its
`@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"]` tag was therefore
withdrawn (bead `flapjack-2s5`). This module supplies the faithful carrier
`PanToCrepVarsExact`, whose `vars` field is the reviewed canonical translation
`HolFiniteMapExact` of a HOL finite map (`fmap_as_finite_support` qualifier), and
states `expHdlExact` over it with the exact HOL clauses. The broad carrier
`PanToCrepVarsBroad` and the kernel roundtrip `holFmapAsFiniteSupportWitness`
witness that the exact carrier is the canonical finite-support translation of
the raw lookup function.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL)

/-- The broad, raw-function carrier for the `exp_hdl` variable map: the same
    shape as the production `FiniteMap MlS (ShapeHOL × List Nat)` parameter of
    `expHdlHOL`, with no finite-support guarantee. Flapjack-only infrastructure
    used as the broad counterpart of `PanToCrepVarsExact`. -/
structure PanToCrepVarsBroad where
  vars : MlS → Option (ShapeHOL × List Nat)

/-- The reviewed exact carrier: the `exp_hdl` variable map as a canonical
    `HolFiniteMapExact`, i.e. the standard Lean translation of a HOL finite map
    `varname |-> (shape # num list)`. Flapjack-only representation
    infrastructure; the qualifier on `expHdlExact` records that translation. -/
structure PanToCrepVarsExact where
  vars : HolFiniteMapExact MlS (ShapeHOL × List Nat)

namespace PanToCrepVarsExact

/-- Project the exact carrier onto its broad raw-function counterpart. -/
def toBroad (state : PanToCrepVarsExact) : PanToCrepVarsBroad :=
  ⟨state.vars.lookup⟩

/-- Reconstruct the exact carrier from a broad raw function plus a finite
    support witness (the canonical-translation roundtrip direction). -/
def ofBroad (state : PanToCrepVarsBroad)
    (h : ∃ keys : List MlS, ∀ key, state.vars key ≠ none → key ∈ keys) :
    PanToCrepVarsExact :=
  ⟨⟨state.vars, h⟩⟩

/-- The canonical finite-support witness for this module: the exact carrier is
    the HOL finite-map translation of its broad raw-function counterpart, with
    `ofBroad (toBroad state) = state`. Kernel-checked; the `fmap_as_finite_support`
    checker requires this declaration beside `expHdlExact`. -/
theorem holFmapAsFiniteSupportWitness (state : PanToCrepVarsExact) :
    ofBroad (toBroad state) state.vars.finiteSupport = state := by
  cases state
  rfl

end PanToCrepVarsExact

/-- Cake's `exp_hdl` over the exact finite-map carrier.

    HOL (`cakeml/pancake/pan_to_crepScript.sml:106-112`) is
    `exp_hdl fm v = case FLOOKUP fm v of
      | NONE => Skip
      | SOME (vshp, ns) => nested_seq (MAP2 Assign ns (load_globals 0w (LENGTH ns)))`.
    Here `vshp` is discarded, `FLOOKUP` reads `context.vars.lookup`,
    `nested_seq` is `crepNestedSeqHOL`, `MAP2 Assign` is `panMap2`, and
    `load_globals 0w n` is `loadGlobalsHOL 0w n`, so the clauses match
    clause-for-clause over the reviewed finite-map translation. The statement is
    tagged with the `fmap_as_finite_support` qualifier because `vars` is a field
    of the same-module carrier `PanToCrepVarsExact` typed by
    `HolFiniteMapExact`, with the canonical witness above. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"
  (fmap_as_finite_support := [vars])]
def expHdlExact {width : Nat} [NeZero width] (context : PanToCrepVarsExact)
    (v : MlS) : CrepProgHOL width :=
  match context.vars.lookup v with
  | none => .skip
  | some (_, names) =>
      crepNestedSeqHOL
        (panMap2 (fun destination source => .assign destination source)
          names (loadGlobalsHOL (0 : BitVec 5) names.length))

/-- Consumer bridge: the exact `expHdlExact` agrees with the untagged raw-map
    `expHdlHOL` whenever the raw function has a finite support. This connects the
    faithful carrier to the existing production bridge
    `crepProgToHOL_expHdlFiniteMap` without introducing a third unrelated
    variant. -/
theorem expHdlExact_eq_expHdlHOL {width : Nat} [NeZero width]
    (fm : MlS → Option (ShapeHOL × List Nat))
    (h : ∃ keys : List MlS, ∀ key, fm key ≠ none → key ∈ keys) (v : MlS) :
    expHdlExact (width := width) ⟨⟨fm, h⟩⟩ v = expHdlHOL fm v := by
  cases hlookup : fm v <;> rfl

end Flapjack
