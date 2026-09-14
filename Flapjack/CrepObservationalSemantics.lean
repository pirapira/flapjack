import Flapjack.CrepEvaluate
import Flapjack.LoopObservationalSemantics

/-!
# Crepe `semantics`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:448-472`.

The source semantics observes every clock-indexed call evaluation.  A run
which produces an error/control/empty result is a failure; a Return or
FinalFFI witness terminates; otherwise the clock-indexed I/O traces are
assembled with the source prefix LUB.  The LUB structure is shared with the
already source-shaped prefix implementation, without changing its relation.
-/

namespace Flapjack

inductive CrepSemanticResult (α : Type u) where
  | error
  | timeOut
  | broke (label : Nat)
  | continued (label : Nat)
  | returned (values : List α)
  | raised (exception : α)
  | finalFfi (event : FfiFinalEvent)
  deriving DecidableEq, Repr

def crepControlResultToSemantic :
    Option (CrepControlResult α) → Option (CrepSemanticResult α)
  | none => none
  | some (.normal _) => none
  | some (.returned _ values) => some (.returned values)
  | some (.raised _ exception) => some (.raised exception)
  | some (.broke _ label) => some (.broke label)
  | some (.continued _ label) => some (.continued label)
  | some (.finalFfi _ event) => some (.finalFfi event)

abbrev CrepLprefixLub (family : Nat → List FfiEvent) :=
  LoopLprefixLub family

def crepLprefixChain (family : Nat → List FfiEvent) : Prop :=
  loopLprefixChain family

noncomputable def crepBuildLprefixLub (family : Nat → List FfiEvent)
    (chain : crepLprefixChain family) : CrepLprefixLub family :=
  buildLoopLprefixLub family chain

inductive CrepSemanticOutcome where
  | success
  | ffi (outcome : FfiOutcome)
  deriving DecidableEq, Repr

inductive CrepBehaviour where
  | diverge (family : Nat → List FfiEvent)
      (trace : CrepLprefixLub family)
  | terminate (outcome : CrepSemanticOutcome) (events : List FfiEvent)
  | fail

structure CrepSemanticsHooks (α : Type u) where
  evaluate : Nat → Option (CrepSemanticResult α) × CrepState α
  ioEvents : CrepState α → List FfiEvent

def crepResultOutcome (result : Option (CrepSemanticResult α)) :
    Option CrepSemanticOutcome :=
  match result with
  | some (.returned _) => some .success
  | some (.finalFfi event) => some (.ffi event.outcome)
  | _ => none

def crepForbiddenResult : Option (CrepSemanticResult α) → Prop
  | some .timeOut | some (.finalFfi _) | some (.returned _) => False
  | _ => True

def crepHasForbiddenRun (hooks : CrepSemanticsHooks α) : Prop :=
  ∃ clock, crepForbiddenResult (hooks.evaluate clock).1

def crepHasSuccessfulRun (hooks : CrepSemanticsHooks α) : Prop :=
  ∃ clock result state outcome,
    hooks.evaluate clock = (result, state) ∧
    crepResultOutcome result = some outcome

noncomputable def crepChooseTermination
    (hooks : CrepSemanticsHooks α)
    (witness : crepHasSuccessfulRun hooks) : CrepBehaviour :=
  let _clock := Classical.choose witness
  let resultWitness := Classical.choose_spec witness
  let _result := Classical.choose resultWitness
  let stateWitness := Classical.choose_spec resultWitness
  let state := Classical.choose stateWitness
  let outcomeWitness := Classical.choose_spec stateWitness
  let outcome := Classical.choose outcomeWitness
  .terminate outcome (hooks.ioEvents state)

noncomputable def crepSemanticsWithLub
    (hooks : CrepSemanticsHooks α)
    (divergenceLub : CrepLprefixLub
      (fun clock => hooks.ioEvents (hooks.evaluate clock).2)) : CrepBehaviour :=
  by
    classical
    exact if forbidden : crepHasForbiddenRun hooks then
      .fail
    else if successful : crepHasSuccessfulRun hooks then
      crepChooseTermination hooks successful
    else
      .diverge _ divergenceLub

noncomputable def crepSemantics
    (hooks : CrepSemanticsHooks α)
    (divergenceChain : crepLprefixChain
      (fun clock => hooks.ioEvents (hooks.evaluate clock).2)) : CrepBehaviour :=
  crepSemanticsWithLub hooks (crepBuildLprefixLub _ divergenceChain)

def crepEvaluateHooks
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (state : CrepState α) :
    CrepSemanticsHooks α where
  evaluate clock :=
    (crepControlResultToSemantic
      (crepEvaluate functions primitive ffi sharedMem
        baseAddress topAddress clock state
        (.call none "main" [])), state)
  ioEvents := fun _ => []

end Flapjack
