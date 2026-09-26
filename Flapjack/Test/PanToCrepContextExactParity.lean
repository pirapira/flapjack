import Flapjack.Pancake.PanToCrep.ContextExact

/-!
Kernel checks for the exact Pan-to-Crep context's finite-map fields and the
canonical finite-support roundtrip. Field payloads match the direct HOL
`mk_ctxt_fields` record row in `scripts/hol-probes/compile_to_crep_probe.out`.
-/

namespace Flapjack.Test.PanToCrepContextExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL)

private def p : MlS := Flapjack.Basis.Pure.MlString.ofString "p"
private def f : MlS := Flapjack.Basis.Pure.MlString.ofString "f"
private def e : MlS := Flapjack.Basis.Pure.MlString.ofString "E"

private def sample : PanToCrepContextExact 8 where
  vars := (HolFiniteMapExact.empty).update (p, (.one, [0]))
  funcs := (HolFiniteMapExact.empty).update (f, ([(p, .one)], .one))
  eids := (HolFiniteMapExact.empty).update (e, (2 : BitVec 8))
  vmax := 3

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

end Flapjack.Test.PanToCrepContextExactParity
