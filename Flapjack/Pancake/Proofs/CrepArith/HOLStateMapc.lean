import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Proofs.CrepArith

/-!
# Crep arithmetic proof-script state updates

The `mapc` overload and its `FLOOKUP_mapc` equation are local to
`crep_arithProofScript.sml:109`. They live under the `CrepArith` counterpart,
while the carrier itself remains in `Semantics.CrepSem.HOLState`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- HOL's local `mapc f` state update, using `FMAP_MAP2` on the code map. -/
def CrepSemHOLState.mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLState.FLOOKUP_mapc {width : Nat} [NeZero width]
    {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : MlString) :
    (state.mapc f).code.lookup name =
      (state.code.lookup name).map (fun entry => f (name, entry)) := rfl

@[simp] theorem CrepSemHOLState.toExpressionEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toExpressionEvaluatorState =
      state.toExpressionEvaluatorState := by
  rfl

/-- Changing only the HOL code map cannot alter expression evaluation after
projection into the source evaluator. This is Flapjack support for the
`simp_exp_correct1` dependency; the evaluator correspondence to native HOL
remains unproved. -/
theorem evalCrepHolFiniteWordSourceExp_mapc_projection
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]

/-- All-positive-width `simp_exp_correct1` support over the HOL-shaped Crep
state carrier and the proof-script-local `mapc` update. The statement keeps
the unused word_lab result binder, a successful full word_lab evaluation
premise, the exact code-map update, the `n2w` simplifier image, and the full
optional word_lab equality. It remains untagged because evaluation is through
the explicit finite-width source projection rather than native HOL
`crepSem$eval`; this theorem does not establish the finite-index instance or
recursive evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateSource
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool))
    (_result : PanWordLab (Fin width → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState expression ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (state.mapc update).toExpressionEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord
          (instFinHolFiniteDimension (width := width))
          (BitVec.ofNat
            (HolFiniteDimension.width (Fin width)) n)) expression) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  letI : HolFiniteDimension (Fin width) :=
    instFinHolFiniteDimension (width := width)
  have hCodeId :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        state.toExpressionEvaluatorState = state.toExpressionEvaluatorState := by
    cases state.toExpressionEvaluatorState
    simp [crepArithHolFiniteDimensionMapCode]
  have hSource := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := instFinHolFiniteDimension (width := width))
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    state.toExpressionEvaluatorState expression
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hSource
  exact hSource

end Flapjack
