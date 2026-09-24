import Flapjack.Pancake.PanStatic

/-!
# `panLang$is_wf_shape` parity

The expected booleans are the checked-in HOL-EVAL observations from
`scripts/hol-probes/pan_lang_wf_shape_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:139-144`.

Two predicates are checked:

* the production `isWfShape` over the cache-augmented `StructContext`, and
* the exact HOL-shaped port `isWfShapeHOL` over `StructContextHOL`, related to
  the production predicate by the checked adapter `isWfShapeHOL_toHOL`.
-/

namespace Flapjack.Test.PanLangWfShapeParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:139-144 (is_wf_shape_def)"

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def pairContextHOL : StructContextHOL :=
  pairContext.toHOL

def parityGuard : Bool :=
  isWfShape [] .one &&
  isWfShape [] (.comb []) &&
  isWfShape pairContext (.named "Pair") &&
  !(isWfShape pairContext (.named "Missing")) &&
  isWfShape pairContext (.comb [.one, .named "Pair", .comb [.one]]) &&
  !(isWfShape pairContext (.comb [.named "Pair", .named "Missing"]))

/-- The exact HOL-shaped port reproduces the same six direct HOL rows. -/
def exactParityGuard : Bool :=
  isWfShapeHOL [] .one &&
  isWfShapeHOL [] (.comb []) &&
  isWfShapeHOL pairContextHOL (.named "Pair") &&
  !(isWfShapeHOL pairContextHOL (.named "Missing")) &&
  isWfShapeHOL pairContextHOL (.comb [.one, .named "Pair", .comb [.one]]) &&
  !(isWfShapeHOL pairContextHOL (.comb [.named "Pair", .named "Missing"]))

/-- The exact port and the production predicate agree through the context
    projection, for every shape. -/
theorem exactAgreement (shape : Shape) :
    isWfShapeHOL pairContextHOL shape = isWfShape pairContext shape :=
  isWfShapeHOL_toHOL pairContext shape

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:139-144 (is_wf_shape_def)"
#eval parityGuard
#guard parityGuard
#eval exactParityGuard
#guard exactParityGuard

/-- Build/executable regression: the production `isWfShape` and the exact
    HOL-shaped `isWfShapeHOL` both reproduce the six checked-in direct HOL rows,
    and the two agree through the checked context adapter. -/
def runChecks : IO Bool := do
  if parityGuard && exactParityGuard then
    IO.println "PASS panLang is_wf_shape parity (6 HOL rows)"
    pure true
  else
    IO.println "FAIL panLang is_wf_shape parity"
    pure false

end Flapjack.Test.PanLangWfShapeParity