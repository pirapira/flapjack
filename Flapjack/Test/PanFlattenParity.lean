import Flapjack.PanValues

/-!
# Pancake value-flattening parity

The expected lists are from the direct HOL probe in
`scripts/hol-probes/pan_flatten_probe.out`, evaluating `flatten_def` in
`cakeml/pancake/semantics/panSemScript.sml:388-395`.
-/

namespace Flapjack.Test.PanFlattenParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:388-395 (flatten_def)"

def originalWord : List Nat := [3]
def originalRecord : List Nat := [3, 5, 7]
def originalNamed : List Nat := [3, 5, 7]

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:388-395 (flatten_def)"
#guard panValueFlatWords (.word 3) == originalWord
#guard panValueFlatWords (.rStruct [.word 3, .rStruct [.word 5, .word 7]]) ==
  originalRecord
#guard panValueFlatWords
    (.nStruct "Pair" [("left", .word 3),
      ("right", .rStruct [.word 5, .word 7])]) == originalNamed

end Flapjack.Test.PanFlattenParity
