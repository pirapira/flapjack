import Flapjack.CrepToLoop

/-! Direct parity for `crep_to_loop$find_var` (`find_var_def`, line 20). -/
namespace Flapjack.Test.CrepFindVarParity

def context : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def missingVariableUsesCakeFallback : Bool :=
  crepFindVar context 2 == 0

def parityGuard : Bool :=
  crepFindVar context 1 == 5 && missingVariableUsesCakeFallback

#eval parityGuard
#guard missingVariableUsesCakeFallback
#guard parityGuard

end Flapjack.Test.CrepFindVarParity
