import Flapjack.PanValues

/-!
# `panSem` word/value helper parity

The expected values are direct HOL-EVAL results from
`scripts/hol-probes/pan_word_helpers_probeScript.sml`, evaluating
`cakeml/pancake/semantics/panSemScript.sml:28-42`.  They are checked-in
original-implementation facts, not a second Lean oracle.
-/

namespace Flapjack.Test.PanWordParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:28-42 (word/value helpers)"

def originalIsWord : Bool := true
def originalTheWord : Nat := 3
def originalIsValWord : Bool := true
def originalIsValStruct : Bool := false
def originalTheValWord : Option Nat := some 3

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:28-42 (word/value helpers)"

example : panIsWord (PanWordLab.word (3 : Nat)) = originalIsWord := by
  rfl

example : panTheWord (PanWordLab.word (3 : Nat)) = originalTheWord := by
  rfl

example : panIsValWord (PanValue.word (3 : Nat)) = originalIsValWord := by
  rfl

example : panIsValWord
    (PanValue.rStruct [PanValue.word (3 : Nat)]) = originalIsValStruct := by
  rfl

example : panTheValWord (PanValue.word (3 : Nat)) = originalTheValWord := by
  rfl

example : panTheValWord
    (PanValue.rStruct [PanValue.word (3 : Nat)]) = none := by
  rfl

end Flapjack.Test.PanWordParity
