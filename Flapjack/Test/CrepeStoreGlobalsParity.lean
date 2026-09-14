import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$store_globals`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_store_globals_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:109-113`.
-/

namespace Flapjack.Test.CrepeStoreGlobalsParity

open Flapjack

def isEmpty : List (CrepProg Nat) → Bool
  | [] => true
  | _ => false

def isOne : List (CrepProg Nat) → Bool
  | [.storeGlob 3 (.const value)] => value == 7
  | _ => false

def isTwo : List (CrepProg Nat) → Bool
  | [.storeGlob 3 (.const first), .storeGlob 4 (.const second)] =>
      first == 7 && second == 9
  | _ => false

def parityGuard : Bool :=
  isEmpty (storeGlobals 3 1 []) &&
  isOne (storeGlobals 3 1 [.const 7]) &&
  isTwo (storeGlobals 3 1 [.const 7, .const 9])

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (storeGlobals 3 1 []),
    isOne (storeGlobals 3 1 [.const 7]),
    isTwo (storeGlobals 3 1 [.const 7, .const 9])]
  match results with
  | [empty, one, two] =>
      if empty then IO.println "PASS crep store_globals empty" else IO.println "FAIL crep store_globals empty"
      if one then IO.println "PASS crep store_globals one" else IO.println "FAIL crep store_globals one"
      if two then IO.println "PASS crep store_globals two" else IO.println "FAIL crep store_globals two"
      pure (empty && one && two)
  | _ =>
      IO.println "FAIL crep store_globals result arity"
      pure false

end Flapjack.Test.CrepeStoreGlobalsParity
