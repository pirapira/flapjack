import Flapjack.Pancake.PanToCrep.MakeVmapHOL

/-!
# `pan_to_crep$make_vmap` exact finite-map parity

Direct original-HOL oracle rows for the exact tagged finite-map definition
`Flapjack.panToCrepMakeVmapHOLExact` (the Lean counterpart of HOL `pan_to_crep$make_vmap_def`,
`cakeml/pancake/pan_to_crepScript.sml:327-334`). The oracle values are those
recorded by `scripts/hol-probes/compile_to_crep_probe.out` (`make_vmap_shaped`,
`make_vmap_duplicate`, `make_vmap_duplicate_lookup`) produced by running HOL
`pan_to_crep$make_vmap` on the concrete parameter lists in
`scripts/hol-probes/compile_to_crep_probeScript.sml`.

The production path's `String`/`Shape`-keyed `panToCrepMakeVmapHOL` is exercised
separately in `Flapjack/Test/CompileToCrepeParity.lean`; this module exercises
the exact `MlS`/`ShapeHOL` finite-map carrier itself, as required for the
`fmap_as_finite_support_result` port.
-/

namespace Flapjack.Test.PanToCrepMakeVmapParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

/-- Oracle `make_vmap_shaped`: shaped parameters receive consecutive flattened
    slots in source order: `x |-> (One,[0])`, `pair |-> (Comb [One;One],[1;2])`. -/
def makeVmapShapedGuard : Bool :=
  match (panToCrepMakeVmapHOLExact [(ml "x", .one), (ml "pair", .comb [.one, .one])]).lookup (ml "x"),
      (panToCrepMakeVmapHOLExact [(ml "x", .one), (ml "pair", .comb [.one, .one])]).lookup (ml "pair"),
      (panToCrepMakeVmapHOLExact [(ml "x", .one), (ml "pair", .comb [.one, .one])]).lookup (ml "absent") with
  | some (.one, [0]), some (.comb [.one, .one], [1, 2]), none => true
  | _, _, _ => false

/-- Oracle `make_vmap_duplicate_lookup`: the `FEMPTY |++ ZIP` fold gives the
    later duplicate parameter the lookup result: `x |-> (Comb [One;One],[1;2])`.
    This is a deliberately malformed compiler input; the source static checker
    rejects duplicate formal names, but the executable `make_vmap` boundary must
    still agree with the HOL definition. -/
def makeVmapDuplicateGuard : Bool :=
  match (panToCrepMakeVmapHOLExact [(ml "x", .one), (ml "x", .comb [.one, .one])]).lookup (ml "x") with
  | some (.comb [.one, .one], [1, 2]) => true
  | _ => false

/-- The empty parameter list yields the empty finite map. -/
def makeVmapEmptyGuard : Bool :=
  ((panToCrepMakeVmapHOLExact []).lookup (ml "x")).isNone

def makeVmapParityGuard : Bool :=
  makeVmapShapedGuard && makeVmapDuplicateGuard && makeVmapEmptyGuard

#guard makeVmapShapedGuard
#guard makeVmapDuplicateGuard
#guard makeVmapEmptyGuard
#guard makeVmapParityGuard

def runChecks : IO Bool := do
  if makeVmapParityGuard then
    IO.println "PASS exact pan_to_crep make_vmap matches HOL oracle rows"
    pure true
  else
    IO.println "FAIL exact pan_to_crep make_vmap matches HOL oracle rows"
    pure false

end Flapjack.Test.PanToCrepMakeVmapParity
