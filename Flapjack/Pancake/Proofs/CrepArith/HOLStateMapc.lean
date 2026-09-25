import Flapjack.Pancake.Semantics.CrepSem.HOLState

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

end Flapjack
