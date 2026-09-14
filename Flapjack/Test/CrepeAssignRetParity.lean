import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$assign_ret`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_assign_ret_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:122-124`.
-/

namespace Flapjack.Test.CrepeAssignRetParity

open Flapjack

def isEmpty : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def isOne : CrepProg Nat → Bool
  | .seq (.assign 1 (.loadGlob 0)) .skip => true
  | _ => false

def isTwo : CrepProg Nat → Bool
  | .seq (.assign 1 (.loadGlob 0))
      (.seq (.assign 2 (.loadGlob 1)) .skip) => true
  | _ => false

def parityGuard : Bool :=
  isEmpty (assignRet 1 []) &&
  isOne (assignRet 1 [1]) &&
  isTwo (assignRet 1 [1, 2])

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (assignRet 1 []),
    isOne (assignRet 1 [1]),
    isTwo (assignRet 1 [1, 2])]
  match results with
  | [empty, one, two] =>
      if empty then IO.println "PASS crep assign_ret empty" else IO.println "FAIL crep assign_ret empty"
      if one then IO.println "PASS crep assign_ret one" else IO.println "FAIL crep assign_ret one"
      if two then IO.println "PASS crep assign_ret two" else IO.println "FAIL crep assign_ret two"
      pure (empty && one && two)
  | _ =>
      IO.println "FAIL crep assign_ret result arity"
      pure false

end Flapjack.Test.CrepeAssignRetParity
