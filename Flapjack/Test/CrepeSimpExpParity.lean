import Flapjack.CrepeArith

namespace Flapjack.Test.CrepeSimpExpParity

/-! Direct parity for `crep_arith$simp_exp_def`
    (`crep_arithScript.sml:59`).  These cases cover constant folding,
    constant-on-either-side multiplication, recursive children, and the
    unchanged fallback shape. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepSimpExp
      (.crepOp .mul [.const (word8 2), .const (word8 3)]) with
  | .const value => value == word8 6
  | _ => false) &&
  (match crepSimpExp
      (.crepOp .mul [.const (word8 2), .var 2]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp
      (.crepOp .mul [.var 2, .const (word8 2)]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp
      (.crepOp .mul [.var 2, .const (word8 3)]) with
  | .crepOp .mul [.var 2, .const value] => value == word8 3
  | _ => false) &&
  (match crepSimpExp
      (.load (.crepOp .mul [.var 2, .const (word8 2)])) with
  | .load (.shift .lsl (.var 2) (.const value)) => value == word8 1
  | _ => false) &&
  (match crepSimpExp
      (.crepOp .mul
        [.crepOp .mul [.const (word8 2), .const (word8 3)],
         .const (word8 4)]) with
  | .const value => value == word8 24
  | _ => false) &&
  (match crepSimpExp (.var 7 : CrepExp (RiscV.Word 8)) with
  | .var 7 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeSimpExpParity
