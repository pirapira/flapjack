import Flapjack.Crepe
import Flapjack.CrepeInline

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

def argLoadProbe : CrepProg Nat :=
  argLoad [9] [.const 1] [2] (.assign 3 (.const 4))

example (e : CrepExp Nat) (hmem : e ∈ crepExpsOf argLoadProbe) :
    e ∈ [.const 1] ∨ (∃ c, c ∈ [9] ∧ e = .var c) ∨
      e ∈ crepExpsOf (.assign 3 (.const 4)) :=
  crepExpsOf_argLoad [9] [.const 1] [2] (.assign 3 (.const 4)) hmem

def argLoadGuard : Bool :=
  (crepExpsOf argLoadProbe).length == 3

/-! Cake's `exps_of_unreach_elim` (`crep_inlineProofScript.sml:3089`). -/

/-- The expected result pair of eliminating an unreachable tail; spelled out
    literally so the guard does not have to evaluate the well-founded
    `crepUnreachElim` (whose compiled form `#eval` refuses). -/
def unreachElimProbe : CrepProg Nat × Option CrepEarlyExit :=
  ((.return [.const 1] : CrepProg Nat), some .return)

example {q : CrepProg Nat} {r : Option CrepEarlyExit} {e : CrepExp Nat}
    (h : crepUnreachElim
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat) = (q, r))
    (hmem : e ∈ crepExpsOf q) :
    e ∈ crepExpsOf
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat) :=
  crepExpsOf_unreachElim _ h hmem

def unreachElimExpsGuard : Bool :=
  (crepExpsOf unreachElimProbe.1).length == 1 &&
  decide (unreachElimProbe.2 = some .return)

/-! Cake's `exps_of_transform_eoc` (`crep_inlineProofScript.sml:3100`). -/

example {e : CrepExp Nat}
    (hmem : e ∈ crepExpsOf
      (crepTransformEoc [7]
        (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat))) :
    e ∈ crepExpsOf
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat) :=
  crepExpsOf_transformEoc [7] _ hmem

def transformEocExpsGuard : Bool :=
  (crepExpsOf
    (crepTransformEoc [7]
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat))).length == 2

/-! Cake's `exps_of_transform_branch` (`crep_inlineProofScript.sml:3119`). -/

example {e : CrepExp Nat}
    (hmem : e ∈ crepExpsOf
      (crepTransformBranch 0 [7]
        (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat))) :
    e ∈ crepExpsOf
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat) :=
  crepExpsOf_transformBranch 0 [7] _ hmem

def transformBranchExpsGuard : Bool :=
  (crepExpsOf
    (crepTransformBranch 0 [7]
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat))).length == 2

/-! Cake's `mem_var_prog_nested_seq` (`crep_inlineProofScript.sml:2226`). -/

def varProgProgList : List (CrepProg Nat) := [.assign 1 (.const 7), .tick]

example (x : Nat) (hmem : x ∈ crepVarProg (crepNestedSeq varProgProgList)) :
    x ∈ (varProgProgList.map crepVarProg).flatten :=
  (crepVarProg_nestedSeq varProgProgList x).mp hmem

def nestedVarProgGuard : Bool :=
  (crepVarProg (crepNestedSeq varProgProgList)).length ==
    (varProgProgList.map crepVarProg).flatten.length

/-! Cake's `mem_var_prog_transform_eoc` (`crep_inlineProofScript.sml:2241`). -/

example {x : Nat}
    (hmem : x ∈ crepVarProg (crepTransformEoc [7] (.return [.const 1] : CrepProg Nat))) :
    x ∈ crepVarProg (.return [.const 1] : CrepProg Nat) ∨ x ∈ [7] :=
  crepVarProg_transformEoc [7] _ hmem

def transformEocVarProgGuard : Bool :=
  (crepVarProg (crepTransformEoc [7] (.return [.const 1] : CrepProg Nat))).length == 1

/-! Cake's `mem_var_prog_transform_branch` (`crep_inlineProofScript.sml:2258`). -/

example {x : Nat}
    (hmem : x ∈ crepVarProg
      (crepTransformBranch 0 [7] (.return [.const 1] : CrepProg Nat))) :
    x ∈ crepVarProg (.return [.const 1] : CrepProg Nat) ∨ x ∈ [7] :=
  crepVarProg_transformBranch 0 [7] _ hmem

def transformBranchVarProgGuard : Bool :=
  (crepVarProg (crepTransformBranch 0 [7] (.return [.const 1] : CrepProg Nat))).length == 1

/-! Cake's `unreach_elim_preserve_has_return` and
    `unreach_elim_preserve_not_branch_ret`
    (`crep_inlineProofScript.sml:2275,2287`). -/

example {q : CrepProg Nat} {r : Option CrepEarlyExit}
    (hh : crepHasReturn (.seq (.assign 1 (.const 7)) .skip : CrepProg Nat) = false)
    (he : crepUnreachElim (.seq (.assign 1 (.const 7)) .skip : CrepProg Nat) = (q, r)) :
    crepHasReturn q = false :=
  crepUnreachElim_preserve_hasReturn _ hh he

example {q : CrepProg Nat} {r : Option CrepEarlyExit}
    (hh : crepNotBranchRet (.while (.const 1) .skip : CrepProg Nat) = true)
    (he : crepUnreachElim (.while (.const 1) .skip : CrepProg Nat) = (q, r)) :
    crepNotBranchRet q = true :=
  crepUnreachElim_preserve_notBranchRet _ hh he

def hasReturnPreservedGuard : Bool :=
  crepHasReturn (.seq (.assign 1 (.const 7)) .skip : CrepProg Nat) == false &&
  crepNotBranchRet (.while (.const 1) .skip : CrepProg Nat) == true

/-! Cake's `unreach_elim_nested_decs`, `unreach_elim_arg_load` and
    `unreach_elim_arg_load_perm`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1697,1709,1720`). -/

example {r : Option CrepEarlyExit}
    (hfix : crepUnreachElim (.return [.const 1] : CrepProg Nat) =
      ((.return [.const 1] : CrepProg Nat), r)) :
    crepUnreachElim (nestedDecs [1] [.const 7] (.return [.const 1] : CrepProg Nat)) =
      (nestedDecs [1] [.const 7] (.return [.const 1] : CrepProg Nat), r) :=
  crepUnreachElim_nestedDecs [1] [.const 7]
    (.return [.const 1] : CrepProg Nat) r rfl hfix

example {r : Option CrepEarlyExit}
    (hfix : crepUnreachElim (.return [.const 1] : CrepProg Nat) =
      ((.return [.const 1] : CrepProg Nat), r)) :
    crepUnreachElim (argLoad [1] [.const 7] [2] (.return [.const 1] : CrepProg Nat)) =
      (argLoad [1] [.const 7] [2] (.return [.const 1] : CrepProg Nat), r) :=
  crepUnreachElim_argLoad_perm (.return [.const 1] : CrepProg Nat) [1] [.const 7] [2] r
    rfl rfl hfix

def unreachNestedGuard : Bool :=
  (crepVarProg (argLoad [1] [.const 7] [2] (.return [.const 1] : CrepProg Nat))).length == 3

def parityGuard : Bool :=
  isEmpty (crepNestedSeq []) &&
  isOne (crepNestedSeq [.skip]) &&
  isTwo (crepNestedSeq [.tick, .skip]) &&
  isAssignSeq (crepNestedSeq [.assign 1 (.const 7), .assign 2 (.const 9)]) &&
  isFlattened && crepExpsGuard && inlineExpsGuard && argLoadGuard &&
  unreachElimExpsGuard && transformEocExpsGuard && transformBranchExpsGuard &&
  nestedVarProgGuard && transformEocVarProgGuard && transformBranchVarProgGuard &&
  hasReturnPreservedGuard && unreachNestedGuard

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
    inlineExpsGuard,
    argLoadGuard,
    unreachElimExpsGuard,
    transformEocExpsGuard,
    transformBranchExpsGuard,
    nestedVarProgGuard,
    transformEocVarProgGuard,
    transformBranchVarProgGuard,
    hasReturnPreservedGuard,
    unreachNestedGuard]
  match results with
  | [empty, one, two, assignment, flattened, exps, inlineExps, argLoad, unreach, transformEoc, transformBranch, nestedVarProg, transformEocVarProg, transformBranchVarProg, hasReturnPreserved, unreachNested] =>
      if empty then IO.println "PASS crep nested_seq empty" else IO.println "FAIL crep nested_seq empty"
      if one then IO.println "PASS crep nested_seq one" else IO.println "FAIL crep nested_seq one"
      if two then IO.println "PASS crep nested_seq two" else IO.println "FAIL crep nested_seq two"
      if assignment then IO.println "PASS crep nested_seq assignment sequence" else IO.println "FAIL crep nested_seq assignment sequence"
      if flattened then IO.println "PASS crep seqs flatten nested sequences" else IO.println "FAIL crep seqs flatten nested sequences"
      if exps then IO.println "PASS crep nested_seq exps_of" else IO.println "FAIL crep nested_seq exps_of"
      if inlineExps then IO.println "PASS crep inline exps_of membership" else IO.println "FAIL crep inline exps_of membership"
      if argLoad then IO.println "PASS crep inline exps_of arg_load" else IO.println "FAIL crep inline exps_of arg_load"
      if unreach then IO.println "PASS crep inline exps_of unreach_elim" else IO.println "FAIL crep inline exps_of unreach_elim"
      if transformEoc then IO.println "PASS crep inline exps_of transform_eoc" else IO.println "FAIL crep inline exps_of transform_eoc"
      if transformBranch then IO.println "PASS crep inline exps_of transform_branch" else IO.println "FAIL crep inline exps_of transform_branch"
      if nestedVarProg then IO.println "PASS crep inline var_prog nested_seq" else IO.println "FAIL crep inline var_prog nested_seq"
      if transformEocVarProg then IO.println "PASS crep inline var_prog transform_eoc" else IO.println "FAIL crep inline var_prog transform_eoc"
      if transformBranchVarProg then IO.println "PASS crep inline var_prog transform_branch" else IO.println "FAIL crep inline var_prog transform_branch"
      if hasReturnPreserved then IO.println "PASS crep inline unreach_elim preserves has_return" else IO.println "FAIL crep inline unreach_elim preserves has_return"
      if unreachNested then IO.println "PASS crep inline unreach_elim nested_decs/arg_load" else IO.println "FAIL crep inline unreach_elim nested_decs/arg_load"
      pure (empty && one && two && assignment && flattened && exps && inlineExps && argLoad && unreach && transformEoc && transformBranch && nestedVarProg && transformEocVarProg && transformBranchVarProg && hasReturnPreserved && unreachNested)
  | _ =>
      IO.println "FAIL crep nested_seq result arity"
      pure false


/-! `crepUnreachElim_converge` and `crepUnreachElim_fixPoint`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1663` / `:1686`):
    re-eliminating unreachable code is a no-op and the range of
    `crepUnreachElim` is its fixed-point set. -/

example {q : CrepProg Nat} {r : Option CrepEarlyExit}
    (he : crepUnreachElim
      (.seq (.return [.const 1]) (.assign 4 (.const 9)) : CrepProg Nat) = (q, r)) :
    crepUnreachElim q = (q, r) :=
  crepUnreachElim_converge _ he

example (q : CrepProg Nat) (r : Option CrepEarlyExit)
    (hq : crepUnreachElim q = (q, r)) :
    ∃ p : CrepProg Nat, crepUnreachElim p = (q, r) :=
  (crepUnreachElim_fixPoint q r).mpr hq

end Flapjack.Test.CrepeNestedSeqParity
