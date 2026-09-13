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
fuel value.  Since core Lean has no CakeML `llist`/`build_lprefix_lub`, the
divergence result retains the exact clock-indexed image as
`LoopLprefixLub.fromClock`.
-/

namespace Flapjack

inductive LoopSemanticOutcome where
  | success
  | ffi (outcome : FfiOutcome)
  deriving DecidableEq, Repr

structure LoopLprefixLub (α : Type u) where
  fromClock : Nat → List α

inductive LoopBehaviour where
  | diverge (trace : LoopLprefixLub FfiEvent)
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

def loopBuildLprefixLub (hooks : LoopSemanticsHooks) : LoopLprefixLub FfiEvent :=
  { fromClock := fun clock => hooks.ioEvents (hooks.evaluate clock).2 }

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

/-! Exact observational counterpart of `semantics_def`. -/
noncomputable def loopSemantics (hooks : LoopSemanticsHooks) : LoopBehaviour :=
  by
    classical
    exact if forbidden : loopHasForbiddenRun hooks then
      .fail
    else if successful : loopHasSuccessfulRun hooks then
      loopChooseTermination hooks successful
    else
      .diverge (loopBuildLprefixLub hooks)

end Flapjack
