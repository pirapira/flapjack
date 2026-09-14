import Flapjack.PanEvaluate
import Flapjack.LoopObservationalSemantics

/-!
# Pancake `panSem.semantics`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:785-809`
(`semantics_def`).  The source repeatedly evaluates
`Call NONE start []` at clock-indexed states, fails when a run is neither a
timeout/final-FFI/return observation nor a permitted residual run, chooses a
successful `Return` or `FinalFFI` witness, and otherwise returns the
`build_lprefix_lub` of the clock-indexed FFI-event prefixes.

The prefix-LUB relation is shared with the already source-shaped loop
semantics port; the aliases below keep the Pancake boundary source-named
without introducing a second divergent LUB proof.
-/

namespace Flapjack

abbrev PanLList (α : Type u) := LoopLList α
abbrev PanLprefixLubPredicate (family : Nat → List α) (trace : PanLList α) : Prop :=
  LoopLprefixLubPredicate family trace
abbrev PanLprefixLub (family : Nat → List α) := LoopLprefixLub family
abbrev panLprefixChain (family : Nat → List α) : Prop := loopLprefixChain family

noncomputable def buildPanLprefixLub (family : Nat → List α)
    (chain : panLprefixChain family) : PanLprefixLub family :=
  buildLoopLprefixLub family chain

inductive PanSemanticOutcome where
  | success
  | ffi (outcome : FfiOutcome)
  deriving DecidableEq, Repr

inductive PanBehaviour where
  | diverge (family : Nat → List FfiEvent)
      (trace : PanLprefixLub family)
  | terminate (outcome : PanSemanticOutcome) (events : List FfiEvent)
  | fail

structure PanSemanticsHooks (α : Type u) (σ : Type v) where
  evaluate : Nat → Option (PanValueFfiClockResult α σ)
  ffiOutcome : FfiFinalEvent → FfiOutcome

def panResultFfi : PanValueFfiClockResult α σ → FfiState σ
  | (.control (.normal _ _ _ ffi), _) => ffi
  | (.control (.returned _ _ _ ffi _), _) => ffi
  | (.control (.raised _ _ _ ffi _ _), _) => ffi
  | (.control (.broke _ _ _ ffi), _) => ffi
  | (.control (.continued _ _ _ ffi), _) => ffi
  | (.control (.finalFfi _ _ _ ffi _), _) => ffi
  | (.timeout _ _ _ ffi, _) => ffi

def panResultEvents : Option (PanValueFfiClockResult α σ) → List FfiEvent
  | some result => (panResultFfi result).ioEvents
  | none => []

def panResultOutcome (hooks : PanSemanticsHooks α σ)
    (result : Option (PanValueFfiClockResult α σ)) :
    Option PanSemanticOutcome :=
  match result with
  | some (.control (.returned _ _ _ _ _), _) => some .success
  | some (.control (.finalFfi _ _ _ _ event), _) =>
      some (.ffi (hooks.ffiOutcome event))
  | _ => none

def panForbiddenResult : Option (PanValueFfiClockResult α σ) → Prop
  | some (.timeout _ _ _ _, _) => False
  | some (.control (.finalFfi _ _ _ _ _), _) => False
  | some (.control (.returned _ _ _ _ _), _) => False
  | _ => True

def panHasForbiddenRun (hooks : PanSemanticsHooks α σ) : Prop :=
  ∃ clock, panForbiddenResult (hooks.evaluate clock)

def panHasSuccessfulRun (hooks : PanSemanticsHooks α σ) : Prop :=
  ∃ clock result outcome,
    hooks.evaluate clock = some result ∧
      panResultOutcome hooks (some result) = some outcome

noncomputable def panChooseTermination (hooks : PanSemanticsHooks α σ)
    (witness : panHasSuccessfulRun hooks) : PanBehaviour :=
  let _clock := Classical.choose witness
  let resultWitness := Classical.choose_spec witness
  let result := Classical.choose resultWitness
  let outcomeWitness := Classical.choose_spec resultWitness
  let outcome := Classical.choose outcomeWitness
  .terminate outcome (panResultEvents (some result))

noncomputable def panSemanticsWithLub (hooks : PanSemanticsHooks α σ)
    (divergenceLub : PanLprefixLub
      (fun clock => panResultEvents (hooks.evaluate clock))) : PanBehaviour :=
  by
    classical
    exact if forbidden : panHasForbiddenRun hooks then
      .fail
    else if successful : panHasSuccessfulRun hooks then
      panChooseTermination hooks successful
    else
      .diverge _ divergenceLub

noncomputable def panSemantics (hooks : PanSemanticsHooks α σ)
    (divergenceChain : panLprefixChain
      (fun clock => panResultEvents (hooks.evaluate clock))) : PanBehaviour :=
  panSemanticsWithLub hooks
    (buildPanLprefixLub _ divergenceChain)

end Flapjack
