import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$var_cexp`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_var_cexp_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:128-142`.
-/

namespace Flapjack.Test.CrepeVarCexpParity

open Flapjack

def parityGuard : Bool :=
  crepExpVars (.const (7 : Nat)) == [] &&
  crepExpVars (.var 3 : CrepExp Nat) == [3] &&
  crepExpVars (.load (.load32 (.var 3)) : CrepExp Nat) == [3] &&
  crepExpVars (.loadGlob 4 : CrepExp Nat) == [] &&
  crepExpVars (.op .add [.var 3, .const 7, .var 4] : CrepExp Nat) == [3, 4] &&
  crepExpVars (.cmp .equal (.var 3) (.loadByte (.var 4)) : CrepExp Nat) == [3, 4] &&
  crepExpVars (.baseAddr : CrepExp Nat) == [] &&
  crepExpVars (.topAddr : CrepExp Nat) == []

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep var_cexp constants, variables, loads, globals, ops, comparisons, and addresses"
  else
    IO.println "FAIL crep var_cexp parity"
  pure parityGuard

end Flapjack.Test.CrepeVarCexpParity
