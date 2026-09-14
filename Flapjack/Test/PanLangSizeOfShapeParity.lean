import Flapjack.Language

/-!
# `panLang$size_of_shape` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_size_of_shape_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:174-178`.
-/

namespace Flapjack.Test.PanLangSizeOfShapeParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:174-178 (size_of_shape_def)"

def parityGuard : Bool :=
  Shape.shapeSize .one == 1 &&
  Shape.shapeSize (.comb []) == 0 &&
  Shape.shapeSize (.named "Pair") == 1 &&
  Shape.shapeSize (.comb [.one, .comb [.one, .one], .named "Pair"]) == 4

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:174-178 (size_of_shape_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangSizeOfShapeParity
