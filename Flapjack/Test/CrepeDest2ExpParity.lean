import Flapjack.CrepeArith

namespace Flapjack.Test.CrepeDest2ExpParity

/-! Direct parity for `crep_arith$dest_2exp_def`
    (`crep_arithScript.sml:15`).  These cases cover the zero, one, even,
    odd, and repeated-even branches of the original recursive definition. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (crepDest2Exp (word8 0) == none) &&
  (crepDest2Exp (word8 1) == some 0) &&
  (crepDest2Exp (word8 2) == some 1) &&
  (crepDest2Exp (word8 4) == some 2) &&
  (crepDest2Exp (word8 8) == some 3) &&
  (crepDest2Exp (word8 3) == none) &&
  (crepDest2Exp (word8 6) == none) &&
  (crepDest2Exp (word8 255) == none)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeDest2ExpParity
