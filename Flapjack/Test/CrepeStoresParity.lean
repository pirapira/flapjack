import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$stores`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_stores_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:95-100`.
-/

namespace Flapjack.Test.CrepeStoresParity

open Flapjack

def isEmpty : List (CrepProg Nat) → Bool
  | [] => true
  | _ => false

def isZeroTwo : List (CrepProg Nat) → Bool
  | [.store (.var 3) (.const first),
     .store (.op .add [.var 3, .const firstOffset]) (.const second)] =>
      first == 7 && firstOffset == 4 && second == 9
  | _ => false

def isNonzeroTwo : List (CrepProg Nat) → Bool
  | [.store (.op .add [.var 3, .const firstOffset]) (.const first),
     .store (.op .add [.var 3, .const secondOffset]) (.const second)] =>
      firstOffset == 4 && first == 7 && secondOffset == 8 && second == 9
  | _ => false

def parityGuard : Bool :=
  isEmpty (stores (.var 3) [] 0 4) &&
  isZeroTwo (stores (.var 3) [.const 7, .const 9] 0 4) &&
  isNonzeroTwo (stores (.var 3) [.const 7, .const 9] 4 4)

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (stores (.var 3) [] 0 4),
    isZeroTwo (stores (.var 3) [.const 7, .const 9] 0 4),
    isNonzeroTwo (stores (.var 3) [.const 7, .const 9] 4 4)]
  match results with
  | [empty, zeroTwo, nonzeroTwo] =>
      if empty then IO.println "PASS crep stores empty" else IO.println "FAIL crep stores empty"
      if zeroTwo then IO.println "PASS crep stores zero offset" else IO.println "FAIL crep stores zero offset"
      if nonzeroTwo then IO.println "PASS crep stores nonzero offset" else IO.println "FAIL crep stores nonzero offset"
      pure (empty && zeroTwo && nonzeroTwo)
  | _ =>
      IO.println "FAIL crep stores result arity"
      pure false

end Flapjack.Test.CrepeStoresParity
