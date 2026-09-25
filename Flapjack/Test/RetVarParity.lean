import Flapjack.Pancake.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$ret_var`

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/ret_var_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:114-119`.  Both the production `retVar`
(untagged, String names) and the exact `retVarHOL` (tagged `ret_var_def` over
`ShapeHOL`) are checked, together with the `retVarHOL_shapeToHOL` bridge.
-/

namespace Flapjack.Test.RetVarParity

open Flapjack

def parityGuard : Bool :=
  retVar .one [] == none &&
  retVar .one [3, 4] == some 3 &&
  retVar (.comb [.one]) [5] == some 5 &&
  retVar (.comb [.one, .one]) [6] == none &&
  retVar (.named "S") [7] == none

#eval parityGuard
#guard parityGuard

/-! Exact-carrier `retVarHOL` rows mirroring the same HOL fixture. -/

def holParityGuard : Bool :=
  retVarHOL .one [] == none &&
  retVarHOL .one [3, 4] == some 3 &&
  retVarHOL (.comb [.one]) [5] == some 5 &&
  retVarHOL (.comb [.one, .one]) [6] == none &&
  retVarHOL (.named (Flapjack.Basis.Pure.MlString.ofString "S")) [7] == none

#eval holParityGuard
#guard holParityGuard

/-- The exact `retVarHOL` and production `retVar` agree through `shapeToHOL`. -/
example (names : List Nat) :
    retVarHOL (Flapjack.Pancake.PanLang.shapeToHOL (.comb [.one, .one])) names =
      retVar (.comb [.one, .one]) names :=
  retVarHOL_shapeToHOL _ _

/-! Kernel-checked reduction forms of the `Comb` cases, connecting the tagged
`ret_var_def` to `List.head?` (bead `flapjack-pxn.18.2.4.1`). -/

example : retVar (.comb [.one]) [5] = some 5 :=
  retVar_comb_eq_head _ _ (by simp [Shape.shapeSize])

example : retVar (.comb [.one, .one]) [6] = none :=
  retVar_comb_eq_none _ _ (by simp [Shape.shapeSize])

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS ret_var empty/one/comb/named parity"
  else
    IO.println "FAIL ret_var parity"
  pure parityGuard

end Flapjack.Test.RetVarParity
