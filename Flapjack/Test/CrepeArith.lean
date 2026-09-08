import Flapjack.CrepeArith

namespace Flapjack

/-! Executable regressions for the first `crep_arith` slice. -/

def crepArithConstantResult : Option Nat :=
  match crepArithExp
      (.crepOp .mul [.const 7, .const 9] : CrepExp Nat) with
  | .const value => some value
  | _ => none

#guard crepArithConstantResult = some 63

def crepArithNestedResult : Option (Nat × Nat) :=
  match crepArithProg
      (.seq
        (.assign 0 (.crepOp .mul [.const 6, .const 7]))
        (.return [.crepOp .mul [.const 8, .const 5]]) : CrepProg Nat) with
  | .seq (.assign _ (.const first)) (.return [.const second]) =>
      some (first, second)
  | _ => none

#guard crepArithNestedResult = some (42, 40)

end Flapjack
