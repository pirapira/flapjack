import Flapjack.CrepeArith
import Flapjack.RiscV.Model

namespace Flapjack.Test.CrepeDest2ExpParity

open Flapjack.RiscV

/-! Direct parity for `crep_arith$dest_2exp_def`
    (`crep_arithScript.sml:15`). -/
def word (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  crepDest2Exp 0 (word 0) == none &&
  crepDest2Exp 3 (word 1) == some 3 &&
  crepDest2Exp 0 (word 1) == some 0 &&
  crepDest2Exp 0 (word 2) == some 1 &&
  crepDest2Exp 4 (word 4) == some 6 &&
  crepDest2Exp 0 (word 4) == some 2 &&
  crepDest2Exp 0 (word 8) == some 3 &&
  crepDest2Exp 0 (word 3) == none &&
  crepDest2Exp 0 (word 6) == none &&
  crepDest2Exp 0 (word 255) == none

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeDest2ExpParity
