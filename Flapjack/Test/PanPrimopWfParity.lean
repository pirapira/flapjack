import Flapjack.RiscV.PanSemantics
import Flapjack.CrepPrimop

namespace Flapjack.Test.PanPrimopWfParity

open Flapjack
open Flapjack.RiscV

def carryArguments : List (PanValue (Word 64)) :=
  [.word 1, .word 2, .word 0]

def primopWfGuard : Bool :=
  match panPrimitiveHandler .addCarry carryArguments with
  | some value => panValueIsWf ([] : StructContext) value
  | none => false

def primopArityGuard : Bool :=
  (panPrimitiveHandler .addCarry
    [.word (1 : Word 64), .word (2 : Word 64)]).isNone

#eval primopWfGuard
#guard primopWfGuard
#guard primopArityGuard

example : True := by
  match h : panPrimitiveHandler .addCarry carryArguments with
  | some value =>
      have _h := panPrimitiveHandler_isWfShape ([] : StructContext) .addCarry
        carryArguments value h
      trivial
  | none => trivial

/-! Cake's `pan_primop_crep_primop`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096`). -/

example (value : PanValue (Word 64))
    (h : panPrimitiveHandler .addCarry carryArguments = some value) :
    crepPrimitiveHandler .addCarry (panValueFlattenValues carryArguments) =
      some (panValueFlatten value) :=
  panPrimitiveHandler_crepPrimitiveHandler .addCarry carryArguments value h

def crepPrimopGuard : Bool :=
  match panPrimitiveHandler .addCarry carryArguments with
  | some value =>
      crepPrimitiveHandler .addCarry (panValueFlattenValues carryArguments) ==
        some (panValueFlatten value)
  | none => false

#eval crepPrimopGuard
#guard crepPrimopGuard

end Flapjack.Test.PanPrimopWfParity
