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

def isFlattened : Bool :=
  (crepSeqs
      (.seq (.seq .skip .tick) (.assign 3 (.const 7) : CrepProg Nat))).map reprStr ==
    ([.skip, .tick, .assign 3 (.const 7)] : List (CrepProg Nat)).map reprStr

def crepExpsProbe : List (CrepProg Nat) :=
  [.assign 1 (.const 7), .while (.const 1) (.store (.const 2) (.const 3))]

theorem crepExpsOf_nestedSeq_fixture :
    crepExpsOf (crepNestedSeq crepExpsProbe) =
      (crepExpsProbe.map crepExpsOf).flatten :=
  crepExpsOf_nestedSeq crepExpsProbe

def crepExpsGuard : Bool :=
  (crepExpsOf (crepNestedSeq crepExpsProbe)).length == 4 &&
    (crepExpsProbe.map crepExpsOf).flatten.length == 4

def nestedDecsProbe : CrepProg Nat :=
  nestedDecs [1, 2] [.const 1, .const 2] (.assign 3 (.const 4))

def nestedSeqAssignProbe : CrepProg Nat :=
  crepNestedSeq (panMap2 (fun n v => .assign n v) [1, 2] [.const 5, .const 6])

example (e : CrepExp Nat) (hmem : e ∈ crepExpsOf nestedDecsProbe) :
    e ∈ [.const 1, .const 2] ∨ e ∈ crepExpsOf (.assign 3 (.const 4)) :=
  crepExpsOf_nestedDecs [1, 2] [.const 1, .const 2] (.assign 3 (.const 4)) hmem

example (e : CrepExp Nat) (hmem : e ∈ crepExpsOf nestedSeqAssignProbe) :
    e ∈ [.const 5, .const 6] :=
  crepExpsOf_nestedSeq_assign [1, 2] [.const 5, .const 6] hmem

def inlineExpsGuard : Bool :=
  (crepExpsOf nestedDecsProbe).length == 3 &&
    (crepExpsOf nestedSeqAssignProbe).length == 2

def parityGuard : Bool :=
  isEmpty (crepNestedSeq []) &&
  isOne (crepNestedSeq [.skip]) &&
  isTwo (crepNestedSeq [.tick, .skip]) &&
  isAssignSeq (crepNestedSeq [.assign 1 (.const 7), .assign 2 (.const 9)]) &&
  isFlattened && crepExpsGuard && inlineExpsGuard

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (crepNestedSeq []),
    isOne (crepNestedSeq [.skip]),
    isTwo (crepNestedSeq [.tick, .skip]),
    isAssignSeq (crepNestedSeq [.assign 1 (.const 7), .assign 2 (.const 9)]),
    isFlattened,
    crepExpsGuard,
    inlineExpsGuard]
  match results with
  | [empty, one, two, assignment, flattened, exps, inlineExps] =>
      if empty then IO.println "PASS crep nested_seq empty" else IO.println "FAIL crep nested_seq empty"
      if one then IO.println "PASS crep nested_seq one" else IO.println "FAIL crep nested_seq one"
      if two then IO.println "PASS crep nested_seq two" else IO.println "FAIL crep nested_seq two"
      if assignment then IO.println "PASS crep nested_seq assignment sequence" else IO.println "FAIL crep nested_seq assignment sequence"
      if flattened then IO.println "PASS crep seqs flatten nested sequences" else IO.println "FAIL crep seqs flatten nested sequences"
      if exps then IO.println "PASS crep nested_seq exps_of" else IO.println "FAIL crep nested_seq exps_of"
      if inlineExps then IO.println "PASS crep inline exps_of membership" else IO.println "FAIL crep inline exps_of membership"
      pure (empty && one && two && assignment && flattened && exps && inlineExps)
  | _ =>
      IO.println "FAIL crep nested_seq result arity"
      pure false

end Flapjack.Test.CrepeNestedSeqParity
