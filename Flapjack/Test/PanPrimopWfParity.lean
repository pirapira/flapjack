import Flapjack.RiscV.PanSemantics

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

end Flapjack.Test.PanPrimopWfParity
