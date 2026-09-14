import Flapjack.Static

/-!
# `panLang$is_wf_shape` parity

The expected booleans are the checked-in HOL-EVAL observations from
`scripts/hol-probes/pan_lang_wf_shape_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:139-144`.
-/

namespace Flapjack.Test.PanLangWfShapeParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:139-144 (is_wf_shape_def)"

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def parityGuard : Bool :=
  isWfShape [] .one &&
  isWfShape [] (.comb []) &&
  isWfShape pairContext (.named "Pair") &&
  !(isWfShape pairContext (.named "Missing")) &&
  isWfShape pairContext (.comb [.one, .named "Pair", .comb [.one]]) &&
  !(isWfShape pairContext (.comb [.named "Pair", .named "Missing"]))

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:139-144 (is_wf_shape_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangWfShapeParity
