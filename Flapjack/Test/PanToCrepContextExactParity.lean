import Flapjack.Pancake.PanToCrep.ContextBridge

/-!
Kernel checks for the exact Pan-to-Crep context's finite-map fields and the
canonical finite-support roundtrip. Field payloads match the direct HOL
`mk_ctxt_fields` record row in `scripts/hol-probes/compile_to_crep_probe.out`.
-/

namespace Flapjack.Test.PanToCrepContextExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL NameRanged ShapeByteRanged shapeOfHOL)

private def p : MlS := Flapjack.Basis.Pure.MlString.ofString "p"
private def f : MlS := Flapjack.Basis.Pure.MlString.ofString "f"
private def e : MlS := Flapjack.Basis.Pure.MlString.ofString "E"

private def sample : PanToCrepContextExact 8 where
  vars := (HolFiniteMapExact.empty).update (p, (.one, [0]))
  funcs := (HolFiniteMapExact.empty).update (f, ([(p, .one)], .one))
  eids := (HolFiniteMapExact.empty).update (e, (2 : BitVec 8))
  vmax := 3

private def productionVars : FiniteMap String (Shape × List Nat) :=
  FUPDATE FEMPTY ("p", (.one, [0]))

private def productionFuncs : FiniteMap String (List (String × Shape) × Shape) :=
  FUPDATE FEMPTY ("f", ([("p", .one)], .one))

private def productionEids : FiniteMap String (BitVec 8) :=
  FUPDATE FEMPTY ("E", (2 : BitVec 8))

private def productionSample : PanToCrepHOLContext (BitVec 8) where
  vars := productionVars
  funcs := productionFuncs
  eids := productionEids
  vmax := 3

private theorem productionEvidence : PanToCrepContextProductionEvidence productionSample := {
  varsSupport := by
    refine ⟨["p"], ?_⟩
    intro key h
    by_cases hk : "p" == key
    · have heq : "p" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionVars, FUPDATE, FEMPTY, hk] at h
  funcsSupport := by
    refine ⟨["f"], ?_⟩
    intro key h
    by_cases hk : "f" == key
    · have heq : "f" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionFuncs, FUPDATE, FEMPTY, hk] at h
  eidsSupport := by
    refine ⟨["E"], ?_⟩
    intro key h
    by_cases hk : "E" == key
    · have heq : "E" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionEids, FUPDATE, FEMPTY, hk] at h
  varsRanged := by
    intro key value h
    by_cases hk : "p" == key
    · have heq : "p" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionVars, FUPDATE] at h
      subst value
      simp [NameRanged, ShapeByteRanged]
    · simp [productionSample, productionVars, FUPDATE, FEMPTY, hk] at h
  funcsRanged := by
    intro key value h
    by_cases hk : "f" == key
    · have heq : "f" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionFuncs, FUPDATE] at h
      subst value
      simp [NameRanged, ShapeByteRanged]
    · simp [productionSample, productionFuncs, FUPDATE, FEMPTY, hk] at h
  eidsRanged := by
    intro key value h
    by_cases hk : "E" == key
    · have heq : "E" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionEids, FUPDATE] at h
      simp [NameRanged]
    · simp [productionSample, productionEids, FUPDATE, FEMPTY, hk] at h
}

example : sample.vars.lookup p = some (.one, [0]) := by
  simp [sample, p, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.funcs.lookup f = some ([(p, .one)], .one) := by
  simp [sample, f, p, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.eids.lookup e = some (2 : BitVec 8) := by
  simp [sample, e, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.vmax = 3 := rfl

example : PanToCrepContextExact.ofBroad
    (PanToCrepContextExact.toBroad sample) = sample :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness sample

private def bridgedProductionSample :=
  panToCrepContextExactOfProduction productionSample productionEvidence

example : bridgedProductionSample.vars.lookup p = some (.one, [0]) := by
  simp [bridgedProductionSample, productionSample, productionVars, FUPDATE, p,
    panToCrepContextExactOfProduction_vars_lookup,
    Flapjack.Basis.Pure.MlString.toStringOfBytes, Flapjack.Basis.Pure.MlString.ofString,
    Flapjack.Pancake.PanLang.shapeToHOL]

example : bridgedProductionSample.vars.lookup (Flapjack.Basis.Pure.MlString.ofString "missing") = none := by
  simp [bridgedProductionSample, productionSample, productionVars, FUPDATE,
    panToCrepContextExactOfProduction_vars_lookup,
    Flapjack.Basis.Pure.MlString.toStringOfBytes, Flapjack.Basis.Pure.MlString.ofString,
    FEMPTY]

example : ((panToCrepContextExactOfProduction productionSample productionEvidence).vars.lookup
    (Flapjack.Basis.Pure.MlString.ofString "p")).map
      (fun value => (shapeOfHOL value.1, value.2)) = productionSample.vars "p" :=
  panToCrepContextExactOfProduction_vars_lookup_roundtrip productionSample productionEvidence
    "p" (by simp [NameRanged])

example : ((panToCrepContextExactOfProduction productionSample productionEvidence).funcs.lookup
    (Flapjack.Basis.Pure.MlString.ofString "f")).map
      (fun value => (value.1.map (fun parameter =>
        (Flapjack.Basis.Pure.MlString.toStringOfBytes parameter.1, shapeOfHOL parameter.2)),
        shapeOfHOL value.2)) = productionSample.funcs "f" :=
  panToCrepContextExactOfProduction_funcs_lookup_roundtrip productionSample productionEvidence
    "f" (by simp [NameRanged])

example : (panToCrepContextExactOfProduction productionSample productionEvidence).eids.lookup
    (Flapjack.Basis.Pure.MlString.ofString "E") = productionSample.eids "E" :=
  panToCrepContextExactOfProduction_eids_lookup_roundtrip productionSample productionEvidence
    "E" (by simp [NameRanged])

end Flapjack.Test.PanToCrepContextExactParity
