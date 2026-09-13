import Flapjack.PanValues

/-!
# Pancake `res_var` parity

The expected results are from the direct HOL probe in
`scripts/hol-probes/pan_res_var_probe.out`, evaluating `res_var_def` in
`cakeml/pancake/semantics/panSemScript.sml:505-508`.
-/

namespace Flapjack.Test.PanResVarParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:505-508 (res_var_def)"

def locals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 3) else none

def originalDeleteHit : Option (PanValue Nat) := none
def originalDeleteOther : Option (PanValue Nat) := some (.word 3)
def originalUpdateHit : Option (PanValue Nat) := some (.word 7)

def deleteHit : Option (PanValue Nat) :=
  panValueResVar locals "x" none "x"

def deleteOther : Option (PanValue Nat) :=
  panValueResVar locals "y" none "x"

def updateHit : Option (PanValue Nat) :=
  panValueResVar locals "x" (some (.word 7)) "x"

def isWord (value : Option (PanValue Nat)) (expected : Nat) : Bool :=
  match value with
  | some (.word actual) => actual == expected
  | _ => false

def isNone (value : Option (PanValue Nat)) : Bool :=
  match value with
  | none => true
  | some _ => false

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:505-508 (res_var_def)"
#guard isNone deleteHit
#guard isWord deleteOther 3
#guard isWord updateHit 7

end Flapjack.Test.PanResVarParity
