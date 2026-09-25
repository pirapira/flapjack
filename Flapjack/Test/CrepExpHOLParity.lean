import Flapjack.Pancake.CrepLang.Exp

namespace Flapjack.Test.CrepExpHOLParity

open Flapjack

private abbrev E8 := CrepExpHOL 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
private def w5 (n : Nat) : BitVec 5 := BitVec.ofNat 5 n

private def constRow : Bool :=
  match (CrepExpHOL.const (w8 5) : E8) with
  | .const w => w.toNat == 5
  | _ => false

private def varRow : Bool :=
  match (CrepExpHOL.var 7 : E8) with
  | .var n => n == 7
  | _ => false

private def loadRow : Bool :=
  match (CrepExpHOL.load (.const (w8 1)) : E8) with
  | .load _ => true
  | _ => false

private def load32Row : Bool :=
  match (CrepExpHOL.load32 (.const (w8 1)) : E8) with
  | .load32 _ => true
  | _ => false

private def loadByteRow : Bool :=
  match (CrepExpHOL.loadByte (.const (w8 1)) : E8) with
  | .loadByte _ => true
  | _ => false

private def loadGlobRow : Bool :=
  match (CrepExpHOL.loadGlob (w5 7) : E8) with
  | .loadGlob w => w.toNat == 7
  | _ => false

private def opLenRow : Bool :=
  match (CrepExpHOL.op BinOp.add [.const (w8 1), .const (w8 2)] : E8) with
  | .op _ args => args.length == 2
  | _ => false

private def crepOpLenRow : Bool :=
  match (CrepExpHOL.crepOp CrepOp.mul [.const (w8 1)] : E8) with
  | .crepOp _ args => args.length == 1
  | _ => false

private def cmpRow : Bool :=
  match (CrepExpHOL.cmp Cmp.equal (.const (w8 1)) (.const (w8 2)) : E8) with
  | .cmp _ _ _ => true
  | _ => false

private def shiftRow : Bool :=
  match (CrepExpHOL.shift Shift.lsl (.const (w8 1)) (.const (w8 2)) : E8) with
  | .shift _ _ _ => true
  | _ => false

private def baseAddrRow : Bool :=
  match (CrepExpHOL.baseAddr : E8) with
  | .baseAddr => true
  | _ => false

private def topAddrRow : Bool :=
  match (CrepExpHOL.topAddr : E8) with
  | .topAddr => true
  | _ => false

/-- Reproduces the twelve direct HOL EVAL rows in
`scripts/hol-probes/crep_lang_exp_probe.out`. -/
def parityGuard : Bool :=
  constRow && varRow && loadRow && load32Row && loadByteRow && loadGlobRow &&
    opLenRow && crepOpLenRow && cmpRow && shiftRow && baseAddrRow && topAddrRow

#eval parityGuard
#guard parityGuard

example : crepExpToHOL (crepExpOfHOL (CrepExpHOL.const (w8 5) : E8)) =
    (CrepExpHOL.const (w8 5) : E8) := crepExpToHOL_crepExpOfHOL _

example : crepExpOfHOL (crepExpToHOL (CrepExp.const (BitVec.ofNat 8 5) : CrepExp (BitVec 8))) =
    (CrepExp.const (BitVec.ofNat 8 5) : CrepExp (BitVec 8)) :=
  crepExpOfHOL_crepExpToHOL _

end Flapjack.Test.CrepExpHOLParity
