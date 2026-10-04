import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Misc.LprefixLub

/-!
# HOL `wordSem` observational semantics

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:1374-1401`
(bead `flapjack-h29l.9.3`): `semantics_def` over the tagged exact `evaluate`,
using the `llist`/`lprefix_lub` renderings shared with the loopSem and crepSem
semantics ports.
-/

namespace Flapjack

namespace WordSemSemanticsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged definition of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemSemanticsSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `wordSem$semantics_def` (`wordSemScript.sml:1374-1401`):

    ```
    semantics s start =
     let prog = Call NONE (SOME start) [0] NONE in
      if ∃k. case FST(evaluate (prog,s with clock := k)) of
             | SOME (Exception _ _) => T
             | SOME (Result ret _) => ret <> Loc 1 0
             | SOME Error => T
             | NONE => T
             | _ => F
      then Fail
      else
       case some res. ∃k t r outcome.
          evaluate (prog, s with clock := k) = (r,t) ∧
          (case r of
           | (SOME (FinalFFI e)) => outcome = FFI_outcome e
           | (SOME (Result _ _)) => outcome = Success
           | (SOME NotEnoughSpace) => outcome = Resource_limit_hit
           | _ => F) ∧
          res = Terminate outcome t.ffi.io_events
        of
      | SOME res => res
      | NONE => Diverge (build_lprefix_lub
          (IMAGE (λk. fromList (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
    ```

    HOL's `some` is `holOptionSome`, and `build_lprefix_lub`/`fromList` are
    the renderings of HOL's `lprefix_lub`/`llist` libraries.  The set
    `IMAGE f UNIV` is the predicate `fun l => ∃ k, l = f k`.  HOL's `<>` on
    `word_loc` is decided classically.  The definition is noncomputable, as
    HOL's classical definition is. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def semantics {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (start : Nat) : HolBehaviour :=
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  open Classical in
  if ∃ k, (match (evaluate prog { s with clock := k }).1 with
      | some (.exception _ _) => True
      | some (.result ret _) => ret ≠ WordLocW.loc 1 0
      | some .error => True
      | none => True
      | _ => False)
  then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        evaluate prog { s with clock := k } = (r, t) ∧
        (match r with
         | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
         | some (.result _ _) => outcome = HolOutcome.success
         | some .notEnoughSpace => outcome = HolOutcome.resourceLimitHit
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (evaluate prog { s with clock := k }).2.ffi.ioEvents))


/-- Exact HOL `wordSem$word_lang_safe_for_space_def`
    (`wordSemScript.sml:1403-1408`):

    ```
    word_lang_safe_for_space (s:('a,'c,'ffi) wordSem$state) start =
      let prog = Call NONE (SOME start) [0] NONE in
        (∀k res t. wordSem$evaluate (prog, s with clock := k) = (res,t) ==>
          ∃max. t.stack_max = SOME max /\ max <= t.stack_limit)
    ``` -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "word_lang_safe_for_space_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def wordLangSafeForSpace {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (start : Nat) : Prop :=
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  ∀ k res t, evaluate prog { s with clock := k } = (res, t) →
    ∃ max, t.stackMax = some max ∧ max ≤ t.stackLimit

end WordSemStateFiniteExact

end Flapjack
