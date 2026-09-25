import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.CrepeCompileExpVariables

/-!
# Original-domain parity for `pan_to_crep$comp_field`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/comp_field_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:28-33`.
-/

namespace Flapjack.Test.CompFieldParity

open Flapjack

def firstOK : Bool :=
  match compileField 0 [.one, .comb [.one, .one]]
      [.const 1, .const 2, .const 3] with
  | (expressions, .one) => expressions == [.const 1]
  | _ => false

def secondOK : Bool :=
  match compileField 1 [.one, .comb [.one, .one]]
      [.const 1, .const 2, .const 3] with
  | (expressions, .comb [.one, .one]) => expressions == [.const 2, .const 3]
  | _ => false

def fallbackOK : Bool :=
  match compileField 2 [.one] [.const 4] with
  | (expressions, .one) => expressions == [.const 0]
  | _ => false

def holFirstOK : Bool :=
  match compFieldHOL (width := 8) 0
      ([.one, .comb [.one, .one]] : List Flapjack.Pancake.PanLang.ShapeHOL)
      ([.const 1, .const 2, .const 3] : List (CrepExpHOL 8)) with
  | (expressions, .one) => expressions.map crepExpOfHOL == [.const 1]
  | _ => false

def holSecondOK : Bool :=
  match compFieldHOL (width := 8) 1
      ([.one, .comb [.one, .one]] : List Flapjack.Pancake.PanLang.ShapeHOL)
      ([.const 1, .const 2, .const 3] : List (CrepExpHOL 8)) with
  | (expressions, .comb [.one, .one]) =>
      expressions.map crepExpOfHOL == [.const 2, .const 3]
  | _ => false

def holFallbackOK : Bool :=
  match compFieldHOL (width := 8) 2
      ([.one] : List Flapjack.Pancake.PanLang.ShapeHOL)
      ([.const 4] : List (CrepExpHOL 8)) with
  | (expressions, .one) => expressions.map crepExpOfHOL == [.const 0]
  | _ => false

def holEmptyOK : Bool :=
  match compFieldHOL (width := 8) 0
      ([] : List Flapjack.Pancake.PanLang.ShapeHOL)
      ([] : List (CrepExpHOL 8)) with
  | (expressions, .one) => expressions.map crepExpOfHOL == [.const 0]
  | _ => false

def holShortOK : Bool :=
  match compFieldHOL (width := 8) 0
      ([.comb [.one, .one]] : List Flapjack.Pancake.PanLang.ShapeHOL)
      ([.const 5] : List (CrepExpHOL 8)) with
  | (expressions, .comb [.one, .one]) =>
      expressions.map crepExpOfHOL == [.const 5]
  | _ => false

def parityGuard : Bool :=
  firstOK && secondOK && fallbackOK && holFirstOK && holSecondOK &&
    holFallbackOK && holEmptyOK && holShortOK

#eval parityGuard
#guard parityGuard

example :
    (compileField (α := BitVec 8) 1
        [Flapjack.Shape.one, Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]]
        [.const 1, .const 2, .const 3]).1.map crepExpToHOL
      = (compFieldHOL 1
          (List.map Flapjack.Pancake.PanLang.shapeToHOL
            [Flapjack.Shape.one, Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]])
          (List.map crepExpToHOL [.const 1, .const 2, .const 3])).1 :=
  (compileField_map_codecs 1
    [Flapjack.Shape.one, Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]]
    [.const 1, .const 2, .const 3]).1

example :
    ∀ expression ∈
      (compileField 2 [.one] [.const 4]).1,
      expression ∈ ([.const 4] : List (CrepExp Nat)) ∨ expression = .const 0 := by
  intro expression hmem
  exact compileField_mem_or_zero 2 [.one] [.const 4] expression hmem

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS comp_field first/second/fallback"
  else
    IO.println "FAIL comp_field parity"
  pure parityGuard

end Flapjack.Test.CompFieldParity
