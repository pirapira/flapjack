import Flapjack.Pancake.Proofs.CrepArith

namespace Flapjack.Test.CrepeDestConstParity

/-! Direct parity for `crep_arith$dest_const_def`
    (`crep_arithScript.sml:10-12`), observed in
    `scripts/hol-probes/crep_arith_dest_const_probe.out`. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepDestConst (.const (word8 7) : CrepExp (RiscV.Word 8)) with
  | some value => value == word8 7
  | _ => false) &&
  (match crepDestConst (.var 2 : CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false) &&
  (match crepDestConst (.load (.const (word8 3)) : CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false) &&
  (match crepDestConst
      (.crepOp .mul [.const (word8 2), .const (word8 4)] :
        CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false)

#eval parityGuard
#guard parityGuard

example (value : RiscV.Word 8) :
    (.const value : CrepExp (RiscV.Word 8)) = .const value := by
  exact crepDestConstWord_eq_const (.const value) value rfl

example (expression : CrepExp (RiscV.Word 8)) (value : RiscV.Word 8)
    (h : crepDestConst expression = some value) :
    expression = .const value :=
  crepDestConstWord_eq_const expression value h

end Flapjack.Test.CrepeDestConstParity
