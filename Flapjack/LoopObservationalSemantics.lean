import Flapjack.LoopEvaluate
import Flapjack.Ffi

/-!
# Pancake `loopSem.semantics`

This is the observational wrapper from
`cakeml/pancake/semantics/loopSemScript.sml:508-532` (`semantics_def`).
The source evaluates the entry `Call NONE (SOME start) [] NONE` at every
clock, rejects a run family containing `Error`/`NONE`/control results, and
then chooses a successful `Result`/`FinalFFI` witness.  If no witness exists,
it returns the lazy I/O-prefix least upper bound.

`LoopSemanticsHooks.evaluate` is the source entry-call evaluator indexed by
the clock; keeping it explicit prevents this observational definition from
silently replacing the source's clock-indexed quantification with one fixed
fuel value.  `LoopLList` is the finite/infinite lazy-list representation and
`LoopLprefixLubPredicate` is the explicit least-upper-bound relation for the
clock-indexed finite I/O prefixes.
-/

namespace Flapjack

inductive LoopSemanticOutcome where
  | success
  | ffi (outcome : FfiOutcome)
  deriving DecidableEq, Repr

abbrev LoopLList (α : Type u) := Nat → Option α

def loopLListUpperBound (family : Nat → List α) (trace : LoopLList α) : Prop :=
  ∀ clock index value, (family clock)[index]? = some value → trace index = some value

def loopLListLe (left right : LoopLList α) : Prop :=
  ∀ index value, left index = some value → right index = some value

def LoopLprefixLubPredicate (family : Nat → List α) (trace : LoopLList α) : Prop :=
  loopLListUpperBound family trace ∧
    ∀ candidate, loopLListUpperBound family candidate → loopLListLe trace candidate

structure LoopLprefixLub (family : Nat → List α) where
  trace : LoopLList α
  isLub : LoopLprefixLubPredicate family trace

def LoopPrefixChain (family : Nat → List α) : Prop :=
  ∀ clock later, clock ≤ later → family clock <+: family later

theorem loopPrefixValue_unique {family : Nat → List α}
    (hchain : LoopPrefixChain family) {clock later index : Nat} {value laterValue : α}
    (hclock : (family clock)[index]? = some value)
    (hlater : (family later)[index]? = some laterValue) :
    value = laterValue := by
  rcases Nat.le_total clock later with hle | hle
  · have hindex := (List.getElem?_eq_some_iff.mp hclock).choose
    have hsmall := (List.getElem?_eq_some_iff.mp hclock).choose_spec
    have hprefix := hchain clock later hle
    have heq := hprefix.getElem hindex
    have hlater' := (List.getElem?_eq_some_iff.mp hlater).choose_spec
    simpa [hsmall, hlater'] using heq
  · have hindex := (List.getElem?_eq_some_iff.mp hlater).choose
    have hlater' := (List.getElem?_eq_some_iff.mp hlater).choose_spec
    have hprefix := hchain later clock hle
    have heq := hprefix.getElem hindex
    have hsmall := (List.getElem?_eq_some_iff.mp hclock).choose_spec
    simpa [hlater', hsmall] using heq.symm

/-- The `lprefix_chain_nth`/`LUNFOLD` construction from the HOL reference,
represented as a lazy list of optional indexed values. -/
noncomputable def loopPrefixNth (family : Nat → List α) (index : Nat) : Option α :=
  by
    classical
    exact if h : ∃ value clock, (family clock)[index]? = some value then
      some (Classical.choose h)
    else none

noncomputable def buildLoopLprefixLub (family : Nat → List α)
    (hchain : LoopPrefixChain family) : LoopLprefixLub family :=
  by
    classical
    refine { trace := loopPrefixNth family, isLub := ?_ }
    constructor
    · intro clock index value hvalue
      by_cases h : ∃ value' clock', (family clock')[index]? = some value'
      · simp only [loopPrefixNth, dif_pos h]
        exact congrArg some (loopPrefixValue_unique hchain
          (Classical.choose_spec (Classical.choose_spec h)) hvalue)
      · exact (h ⟨value, clock, hvalue⟩).elim
    · intro candidate hbound index value htrace
      by_cases h : ∃ value' clock', (family clock')[index]? = some value'
      · simp only [loopPrefixNth, dif_pos h] at htrace
        have hchosen := Classical.choose_spec (Classical.choose_spec h)
        have hc := hbound _ index (Classical.choose h) hchosen
        have hv : Classical.choose h = value := Option.some.inj htrace
        simpa [hv] using hc
      · simp only [loopPrefixNth, dif_neg h] at htrace
        cases htrace

theorem buildLoopLprefixLub_isLub (family : Nat → List α)
    (hchain : LoopPrefixChain family) :
    LoopLprefixLubPredicate family (buildLoopLprefixLub family hchain).trace :=
  (buildLoopLprefixLub family hchain).isLub

inductive LoopBehaviour where
  | diverge (family : Nat → List FfiEvent)
      (trace : LoopLprefixLub family)
  | terminate (outcome : LoopSemanticOutcome) (events : List FfiEvent)
  | fail

structure LoopSemanticsHooks where
  evaluate : Nat → LoopMachineStep
  ioEvents : LoopMachineState LoopWordLoc → List FfiEvent
  ffiOutcome : LoopWordLoc → FfiOutcome

def loopResultOutcome (hooks : LoopSemanticsHooks)
    (result : Option (LoopMachineResult LoopWordLoc)) :
    Option LoopSemanticOutcome :=
  match result with
  | some (.result _) => some .success
  | some (.finalFfi event) => some (.ffi (hooks.ffiOutcome event))
  | _ => none

def loopForbiddenResult : Option (LoopMachineResult LoopWordLoc) → Prop
  | some .timeOut | some (.finalFfi _) | some (.result _) => False
  | _ => True

def loopHasForbiddenRun (hooks : LoopSemanticsHooks) : Prop :=
  ∃ clock, loopForbiddenResult (hooks.evaluate clock).1

def loopHasSuccessfulRun (hooks : LoopSemanticsHooks) : Prop :=
  ∃ clock result state outcome,
    hooks.evaluate clock = (result, state) ∧
    loopResultOutcome hooks result = some outcome

noncomputable def loopChooseTermination (hooks : LoopSemanticsHooks)
    (witness : loopHasSuccessfulRun hooks) : LoopBehaviour :=
  let _clock := Classical.choose witness
  let resultWitness := Classical.choose_spec witness
  let _result := Classical.choose resultWitness
  let stateWitness := Classical.choose_spec resultWitness
  let state := Classical.choose stateWitness
  let outcomeWitness := Classical.choose_spec stateWitness
  let outcome := Classical.choose outcomeWitness
  .terminate outcome (hooks.ioEvents state)

/-! Exact observational counterpart of `semantics_def` with the source LUB
boundary made explicit for low-level branch proofs. -/
noncomputable def loopSemanticsWithLub (hooks : LoopSemanticsHooks)
    (divergenceLub : LoopLprefixLub
      (fun clock => hooks.ioEvents (hooks.evaluate clock).2)) : LoopBehaviour :=
  by
    classical
    exact if forbidden : loopHasForbiddenRun hooks then
      .fail
    else if successful : loopHasSuccessfulRun hooks then
      loopChooseTermination hooks successful
    else
      .diverge _ divergenceLub

/-! Source-facing wrapper: `semantics_def` constructs the divergence result
with `build_lprefix_lub`; callers provide only the prefix-chain proof. -/
noncomputable def loopSemantics (hooks : LoopSemanticsHooks)
    (divergenceChain : LoopPrefixChain
      (fun clock => hooks.ioEvents (hooks.evaluate clock).2)) : LoopBehaviour :=
  loopSemanticsWithLub hooks (buildLoopLprefixLub _ divergenceChain)

noncomputable def loopSemanticsOfPrefixChain (hooks : LoopSemanticsHooks)
    (hchain : LoopPrefixChain
      (fun clock => hooks.ioEvents (hooks.evaluate clock).2)) : LoopBehaviour :=
  loopSemantics hooks hchain

end Flapjack
