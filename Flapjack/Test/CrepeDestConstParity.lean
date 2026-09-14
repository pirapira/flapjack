import Flapjack.CrepeArith

namespace Flapjack.Test.CrepeDestConstParity

/-! Direct parity for `crep_arith$dest_const_def`
    (`crep_arithScript.sml:10`). -/
def parityGuard : Bool :=
  (match crepDestConst (.const 7 : CrepExp Nat) with
  | some 7 => true
  | _ => false) &&
  (match crepDestConst (.var 2 : CrepExp Nat) with
  | none => true
  | _ => false) &&
  (match crepDestConst (.load (.const 3) : CrepExp Nat) with
  | none => true
  | _ => false) &&
  (match crepDestConst (.crepOp .mul [.const 2, .const 4] : CrepExp Nat) with
  | none => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeDestConstParity
