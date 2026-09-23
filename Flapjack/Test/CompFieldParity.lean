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

def parityGuard : Bool := firstOK && secondOK && fallbackOK

#eval parityGuard
#guard parityGuard

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
