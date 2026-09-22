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

/-! `flookup_res_var_some_eq_lookup` (`panPropsScript.sml:220`) and
    `flookup_res_var_diff_eq_org` (`:228`). -/

theorem panValueResVar_lookup_same_fixture :
    locals "x" = some (.word 3) :=
  panValueResVar_lookup_same locals locals "x" (by simp [panValueResVar, locals])

theorem panValueResVar_lookup_diff_fixture :
    panValueResVar locals "y" none "x" = locals "x" :=
  panValueResVar_lookup_diff locals "y" "x" none (by decide)

def lookupSameGuard : Bool := isWord (locals "x") 3
def lookupDiffGuard : Bool := isWord (panValueResVar locals "y" none "x") 3

#guard lookupSameGuard
#guard lookupDiffGuard

/-! `FLOOKUP_pan_res_var_thm` (`panPropsScript.sml:236`). -/

theorem panValueResVar_eq_ite_fixture :
    panValueResVar locals "y" none "x" =
      (if "x" == "y" then none else locals "x") :=
  panValueResVar_eq_ite locals "y" none "x"

def iteGuard : Bool := isWord (panValueResVar locals "y" none "x") 3

#guard iteGuard

/-! `res_var_commutes'` (`pan_to_crepProofScript.sml:4094`). -/

theorem panValueResVar_comm_fixture :
    panValueResVar (panValueResVar locals "y" none) "x" (some (.word 7)) =
      panValueResVar (panValueResVar locals "x" (some (.word 7))) "y" none :=
  panValueResVar_comm locals "y" "x" none (some (.word 7)) (by decide)

def commGuard : Bool :=
  isWord (panValueResVar (panValueResVar locals "y" none) "x"
      (some (.word 7)) "x") 7 &&
    isNone (panValueResVar (panValueResVar locals "y" none) "x"
      (some (.word 7)) "y")

#eval commGuard
#guard commGuard

/-! `res_var_commutes_strong` (`crep_inlineProofScript.sml:699`). -/

theorem panValueResVar_comm_strong_fixture :
    panValueResVar (panValueResVar locals "x" (locals "x")) "x" (locals "x") =
      panValueResVar (panValueResVar locals "x" (locals "x")) "x" (locals "x") :=
  panValueResVar_comm_strong locals locals "x" "x"

theorem panValueResVar_comm_strong_fixture2 :
    panValueResVar (panValueResVar locals "x" (locals "x")) "y" (locals "y") =
      panValueResVar (panValueResVar locals "y" (locals "y")) "x" (locals "x") :=
  panValueResVar_comm_strong locals locals "x" "y"

def commStrongGuard : Bool :=
  isWord (panValueResVar (panValueResVar locals "x" (locals "x")) "x"
      (locals "x") "x") 3

#eval commStrongGuard
#guard commStrongGuard

/-! `res_var_foldl_commutes_strong` (`crep_inlineProofScript.sml:706`) and
    `flookup_res_var_is_mem_zip_eq` (`crep_inlineProofScript.sml:802`). -/

theorem panValueResVarFold_comm_fixture :
    panValueResVar (panValueResVarFold locals locals ["x", "y"]) "y" (locals "y") =
      panValueResVarFold (panValueResVar locals "y" (locals "y")) locals ["x", "y"] :=
  panValueResVarFold_comm locals locals "y" ["x", "y"]

theorem panValueResVarFold_mem_fixture :
    panValueResVarFold locals locals ["x", "y"] "x" = locals "x" :=
  panValueResVarFold_mem locals locals ["x", "y"] (by simp)

def foldGuard : Bool :=
  isWord (panValueResVarFold locals locals ["x", "y"] "x") 3 &&
    isNone (panValueResVarFold locals locals ["x", "y"] "z")

#eval foldGuard
#guard foldGuard

end Flapjack.Test.PanResVarParity
