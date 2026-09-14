import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$nested_seq`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_nested_seq_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:89-92`.
-/

namespace Flapjack.Test.CrepeNestedSeqParity

open Flapjack

def isEmpty : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def isOne : CrepProg Nat → Bool
  | .seq .skip .skip => true
  | _ => false

def isTwo : CrepProg Nat → Bool
  | .seq .tick (.seq .skip .skip) => true
  | _ => false

def isAssignSeq : CrepProg Nat → Bool
  | .seq (.assign 1 (.const first))
      (.seq (.assign 2 (.const second)) .skip) =>
      first == 7 && second == 9
  | _ => false

def parityGuard : Bool :=
  isEmpty (crepNestedSeq []) &&
  isOne (crepNestedSeq [.skip]) &&
  isTwo (crepNestedSeq [.tick, .skip]) &&
  isAssignSeq (crepNestedSeq [.assign 1 (.const 7), .assign 2 (.const 9)])

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (crepNestedSeq []),
    isOne (crepNestedSeq [.skip]),
    isTwo (crepNestedSeq [.tick, .skip]),
    isAssignSeq (crepNestedSeq [.assign 1 (.const 7), .assign 2 (.const 9)])]
  match results with
  | [empty, one, two, assignment] =>
      if empty then IO.println "PASS crep nested_seq empty" else IO.println "FAIL crep nested_seq empty"
      if one then IO.println "PASS crep nested_seq one" else IO.println "FAIL crep nested_seq one"
      if two then IO.println "PASS crep nested_seq two" else IO.println "FAIL crep nested_seq two"
      if assignment then IO.println "PASS crep nested_seq assignment sequence" else IO.println "FAIL crep nested_seq assignment sequence"
      pure (empty && one && two && assignment)
  | _ =>
      IO.println "FAIL crep nested_seq result arity"
      pure false

end Flapjack.Test.CrepeNestedSeqParity
