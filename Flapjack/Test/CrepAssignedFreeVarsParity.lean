import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$assigned_free_vars`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_assigned_free_vars_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:149-162`.
-/

namespace Flapjack.Test.CrepAssignedFreeVarsParity

open Flapjack

def parityGuard : Bool :=
  crepAssignedFreeVars (.skip : CrepProg Nat) == [] &&
  crepAssignedFreeVars (.assign 7 (.const 3) : CrepProg Nat) == [7] &&
  crepAssignedFreeVars
      (.dec 2 (.const 3)
        (.seq (.assign 2 (.const 4)) (.assign 5 (.const 6))) : CrepProg Nat) == [5] &&
  crepAssignedFreeVars
      (.seq (.assign 1 (.const 3)) (.assign 4 (.const 6)) : CrepProg Nat) == [1, 4] &&
  crepAssignedFreeVars
      (.ite (.const 1) (.assign 1 (.const 3)) (.assign 4 (.const 6)) : CrepProg Nat) == [1, 4] &&
  crepAssignedFreeVars
      (.while (.const 1) (.assign 6 (.const 8)) : CrepProg Nat) == [6] &&
  crepAssignedFreeVars
      (.shMem .load 9 (.const 0) : CrepProg Nat) == [9] &&
  crepAssignedFreeVars
      (.store (.const 0) (.const 1) : CrepProg Nat) == []

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep assigned_free_vars skip/assign/dec/seq/if/while/shmem/fallback"
  else
    IO.println "FAIL crep assigned_free_vars parity"
  pure parityGuard

end Flapjack.Test.CrepAssignedFreeVarsParity
