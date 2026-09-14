import Flapjack.CrepeArith

namespace Flapjack.Test.CrepeMulConstParity

/-! Direct parity for `crep_arith$mul_const_def`
    (`crep_arithScript.sml:50`).  The cases cover the zero, one, power-of-two,
    and general-constant branches of the original definition. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def expression : CrepExp (RiscV.Word 8) := .var 2

def parityGuard : Bool :=
  (match crepMulConst expression (word8 0) with
  | .const value => value == word8 0
  | _ => false) &&
  (match crepMulConst expression (word8 1) with
  | .var 2 => true
  | _ => false) &&
  (match crepMulConst expression (word8 2) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepMulConst expression (word8 3) with
  | .crepOp .mul [.var 2, .const value] => value == word8 3
  | _ => false) &&
  (match crepMulConst expression (word8 4) with
  | .shift .lsl (.var 2) (.const value) => value == word8 2
  | _ => false) &&
  (match crepMulConst expression (word8 8) with
  | .shift .lsl (.var 2) (.const value) => value == word8 3
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeMulConstParity
