import Flapjack.CrepeExpressionStability

namespace Flapjack.Test.CrepeExpressionStabilityParity

open Flapjack

def lookupState : CrepState Nat :=
  { locals := fun n => if n == 3 then some 5 else none
    memory := fun _ => none }

example : ∃ w, lookupState.locals 3 = some w :=
  evalCrepFullExpState_local_lookup_of_mem lookupState 0 0
    (.op .add [.var 3, .const 1]) 6 3
    (by simp [evalCrepFullExpState, lookupState, evalPanBinOp])
    (by simp [crepExpVars, crepExpVars.crepExpVarsList])

#check @evalCrepFullExpState_local_lookup_of_mem

end Flapjack.Test.CrepeExpressionStabilityParity
