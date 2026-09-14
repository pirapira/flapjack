import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$ret_var`

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/ret_var_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:114-119`.
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

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS ret_var empty/one/comb/named parity"
  else
    IO.println "FAIL ret_var parity"
  pure parityGuard

end Flapjack.Test.RetVarParity
