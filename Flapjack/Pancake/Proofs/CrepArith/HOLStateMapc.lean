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

@[simp] theorem CrepSemHOLState.toBitVecEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toBitVecEvaluatorState = state.toBitVecEvaluatorState := rfl

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
the explicit finite-width source projection after translating exact
`CrepExpHOL` syntax to the evaluator carrier, rather than native HOL
`crepSem$eval`; this theorem does not establish the finite-index instance or
recursive evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateSource
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (state.mapc update).toExpressionEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord
          (instFinHolFiniteDimension (width := width))
          (BitVec.ofNat
            (HolFiniteDimension.width (Fin width)) n))
        (crepExpHOLToSourceBits expression)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) := by
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
    state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression)
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hSource
  exact hSource

/-- Production-runtime all-positive-width `simp_exp_correct1` support over the
HOL-shaped state carrier and exact HOL expression syntax. The evaluator in
the premise and conclusion is `evalCrepRuntimeExp`; the source state is
projected to its expression-observable fields and then represented by the
canonical `Fin width` word model. This remains untagged because that
projection fixes code/FFI observations and does not establish the native HOL
state/evaluator or arbitrary `finite_index` correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      (state.mapc update).toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepSimpExp
        (fun n => bitVecToHolWordBits (BitVec.ofNat width n))
        (crepExpHOLToSourceBits expression))).map PanWordLab.word =
    (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  let projected := state.toExpressionEvaluatorState
  have hCodeId :
      crepArithHolWordBitsMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolWordBitsMapCode]
  have hPres := crepSimpExpCorrect1HolWordBits
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    projected (crepExpHOLToSourceBits expression) h
  rw [hCodeId] at hPres
  exact hPres

/-- Direct BitVec production-runtime support for all-positive-width
`crepSemHOLState`. It takes HOL's exact `CrepExpHOL` input and `HolWordLab`
result carrier, and applies the actual HOL-shaped `mapc` update. The evaluator
uses the production RISC-V runtime on a direct word-cell projection, so no
`Fin width → Bool` conversion occurs here. It remains untagged: code/FFI are
fixed in the expression-only projection, and the generic HOL
finite-index/eval_def relation is not established. -/
theorem crepSimpExpCorrect1CrepSemHOLStateBitVecRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab ≠ none) :
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget
        (state.mapc update).toBitVecEvaluatorState.toRuntime)
      (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression))).map
        PanWordLab.word).map PanWordLab.toHolWordLab =
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  let projected := state.toBitVecEvaluatorState
  let productionExpression := crepExpOfHOL expression
  have hRuntime :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word ≠ none := by
    have hWrapped := h
    change ((evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
      productionExpression).map PanWordLab.word).map PanWordLab.toHolWordLab ≠ none
      at hWrapped
    intro hnone
    rw [hnone] at hWrapped
    simp at hWrapped
  have hSource :
      evalCrepHolExpWordLab projected productionExpression ≠ none := by
    rw [evalCrepHolExpWordLab, ← evalCrepRuntimeExp_toRuntime_eq]
    exact hRuntime
  have hCodeId :
      crepArithHolMapCode
        (fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolMapCode]
  have hPres := crepSimpExpCorrect1BitVec
    (f := fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
    projected productionExpression hSource
  rw [hCodeId] at hPres
  have hRuntimePreserved :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        (crepSimpExp (BitVec.ofNat width) productionExpression)).map
          PanWordLab.word =
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word := by
    calc
      _ = evalCrepHolExpWordLab projected
            (crepSimpExp (BitVec.ofNat width) productionExpression) := by
              simp only [evalCrepHolExpWordLab]
              rw [evalCrepRuntimeExp_toRuntime_eq]
      _ = evalCrepHolExpWordLab projected productionExpression := hPres
      _ = _ := by
            simp only [evalCrepHolExpWordLab]
            rw [evalCrepRuntimeExp_toRuntime_eq]
  exact congrArg (Option.map PanWordLab.toHolWordLab) hRuntimePreserved

end Flapjack
