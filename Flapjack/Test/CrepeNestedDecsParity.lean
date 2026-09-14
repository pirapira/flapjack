import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$nested_decs`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_nested_decs_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:102-107`.
-/

namespace Flapjack.Test.CrepeNestedDecsParity

open Flapjack

def isTick : CrepProg Nat → Bool
  | .tick => true
  | _ => false

def isPaired : CrepProg Nat → Bool
  | .dec 1 (.const first) (.dec 2 (.const second) .tick) =>
      first == 7 && second == 9
  | _ => false

def isSkip : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def parityGuard : Bool :=
  isTick (nestedDecs [] [] (.tick : CrepProg Nat)) &&
  isPaired (nestedDecs [1, 2] [.const 7, .const 9] (.tick : CrepProg Nat)) &&
  isSkip (nestedDecs [] [.const 7] (.tick : CrepProg Nat)) &&
  isSkip (nestedDecs [1] [] (.tick : CrepProg Nat))

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isTick (nestedDecs [] [] (.tick : CrepProg Nat)),
    isPaired (nestedDecs [1, 2] [.const 7, .const 9] (.tick : CrepProg Nat)),
    isSkip (nestedDecs [] [.const 7] (.tick : CrepProg Nat)),
    isSkip (nestedDecs [1] [] (.tick : CrepProg Nat))]
  match results with
  | [empty, paired, namesEmpty, valuesEmpty] =>
      if empty then IO.println "PASS crep nested_decs empty" else IO.println "FAIL crep nested_decs empty"
      if paired then IO.println "PASS crep nested_decs paired" else IO.println "FAIL crep nested_decs paired"
      if namesEmpty then IO.println "PASS crep nested_decs empty names" else IO.println "FAIL crep nested_decs empty names"
      if valuesEmpty then IO.println "PASS crep nested_decs empty values" else IO.println "FAIL crep nested_decs empty values"
      pure (empty && paired && namesEmpty && valuesEmpty)
  | _ =>
      IO.println "FAIL crep nested_decs result arity"
      pure false

end Flapjack.Test.CrepeNestedDecsParity
