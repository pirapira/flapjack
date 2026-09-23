import Flapjack.Pancake.Proofs.PanToCrep.Primop

namespace Flapjack.Test.PanCrepPrimopParity

open Flapjack

/-! Direct numeric HOL-EVAL oracle from `pan_crep_primop_probe.out`. -/
def panValid : Bool :=
  match panPrimopHOL .addCarry
      [.word (3 : BitVec 8), .word 4, .word 2] with
  | some (.rStruct [.word result, .word overflow]) =>
      result.toNat == 8 && overflow.toNat == 0
  | _ => false

def panOverflow : Bool :=
  match panPrimopHOL .addCarry
      [.word (255 : BitVec 8), .word 0, .word 1] with
  | some (.rStruct [.word result, .word overflow]) =>
      result.toNat == 0 && overflow.toNat == 1
  | _ => false

def panInvalid : Bool :=
  (panPrimopHOL .addCarry
    [.word (3 : BitVec 8), .rStruct [], .word 0]).isNone

def crepValid : Bool :=
  match crepPrimopHOL .addCarry
      [.word (3 : BitVec 8), .word 4, .word 2] with
  | some [.word result, .word overflow] =>
      result.toNat == 8 && overflow.toNat == 0
  | _ => false

def crepOverflow : Bool :=
  match crepPrimopHOL .addCarry
      [.word (255 : BitVec 8), .word 0, .word 1] with
  | some [.word result, .word overflow] =>
      result.toNat == 0 && overflow.toNat == 1
  | _ => false

def crepInvalid : Bool :=
  (crepPrimopHOL .addCarry
    [.word (3 : BitVec 8), .word 4]).isNone

#guard panValid
#guard panOverflow
#guard panInvalid
#guard crepValid
#guard crepOverflow
#guard crepInvalid

/-- Apply the exact HOL bridge to the nonzero-carry oracle case. -/
theorem bridgeFixture :
    crepPrimopHOL .addCarry
      (([.word (3 : BitVec 8), .word 4, .word 2] :
        List (PanValue (BitVec 8))).flatMap panSemFlattenHOL) =
      some (panSemFlattenHOL
        (.rStruct [.word (8 : BitVec 8), .word 0])) := by
  apply panPrimopCrepPrimop
  rfl

end Flapjack.Test.PanCrepPrimopParity
