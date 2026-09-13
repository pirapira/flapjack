import Flapjack.PanValues

/-!
# `panSem$shape_of` parity

The expected shapes are the checked-in HOL-EVAL results from
`scripts/hol-probes/pan_shape_of_probeScript.sml`, which evaluates
`cakeml/pancake/semantics/panSemScript.sml:80-84`.  The constants below are
the original results, not a second Lean implementation.
-/

namespace Flapjack.Test.PanShapeParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:80-84 (shape_of_def)"

def originalWord : Shape := .one
def originalRStruct : Shape := .comb [.one, .one]
def originalNStruct : Shape := .named "Pair"

def shapeProbeContext : StructContext := []

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:80-84 (shape_of_def)"

example :
    panValueShape shapeProbeContext (.word (3 : Nat)) = originalWord := by
  simp [panValueShape, originalWord]

example :
    panValueShape shapeProbeContext (.rStruct [.word (3 : Nat), .word 5]) =
      originalRStruct := by
  simp [panValueShape, originalRStruct]

example :
    panValueShape shapeProbeContext
        (.nStruct "Pair" [("left", .word (3 : Nat)), ("right", .word 5)]) =
      originalNStruct := by
  simp [panValueShape, originalNStruct]

end Flapjack.Test.PanShapeParity
