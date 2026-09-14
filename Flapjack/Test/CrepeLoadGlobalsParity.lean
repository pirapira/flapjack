import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$load_globals`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_load_globals_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:116-120`.
-/

namespace Flapjack.Test.CrepeLoadGlobalsParity

open Flapjack

def isEmpty : List (CrepExp Nat) → Bool
  | [] => true
  | _ => false

def isOne : List (CrepExp Nat) → Bool
  | [.loadGlob 3] => true
  | _ => false

def isThree : List (CrepExp Nat) → Bool
  | [.loadGlob 3, .loadGlob 4, .loadGlob 5] => true
  | _ => false

def parityGuard : Bool :=
  isEmpty (loadGlobals 3 1 0) &&
  isOne (loadGlobals 3 1 1) &&
  isThree (loadGlobals 3 1 3)

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (loadGlobals 3 1 0),
    isOne (loadGlobals 3 1 1),
    isThree (loadGlobals 3 1 3)]
  match results with
  | [empty, one, three] =>
      if empty then IO.println "PASS crep load_globals empty" else IO.println "FAIL crep load_globals empty"
      if one then IO.println "PASS crep load_globals one" else IO.println "FAIL crep load_globals one"
      if three then IO.println "PASS crep load_globals three" else IO.println "FAIL crep load_globals three"
      pure (empty && one && three)
  | _ =>
      IO.println "FAIL crep load_globals result arity"
      pure false

end Flapjack.Test.CrepeLoadGlobalsParity
