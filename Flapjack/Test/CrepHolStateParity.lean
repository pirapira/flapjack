import Flapjack.Pancake.Semantics.CrepSem.HOLState

namespace Flapjack.Test.CrepHolStateParity

open Flapjack.Basis.Pure.MlString

private def codeName : MlString := .implode []

private def sampleCode : HolFiniteMapExact MlString
    (List Nat × CrepProgHOL 8) where
  lookup name := if name = codeName then some ([], .skip) else none
  finiteSupport := by
    refine ⟨[codeName], ?_⟩
    intro name hlookup
    by_cases h : name = codeName
    · simp [h]
    · simp [h] at hlookup

private def sampleMapc
    (entry : MlString × (List Nat × CrepProgHOL 8)) :
    List Nat × CrepProgHOL 8 := (entry.2.1, .tick)

theorem mapc_lookup_fixture :
    (sampleCode.map2 sampleMapc).lookup codeName = some ([], .tick) := by
  simp [HolFiniteMapExact.map2, sampleCode, sampleMapc, codeName]

def parityGuard : Bool :=
  match (sampleCode.map2 sampleMapc).lookup codeName with
  | some (parameters, .tick) => parameters.isEmpty
  | _ => false

#eval parityGuard

example : parityGuard = true := by rfl

/-- The source evaluator sees identical observable states across HOL `mapc`.
The direct HOL evidence is in `crep_state_mapc_probe.out`. -/
example {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression :=
  evalCrepHolFiniteWordSourceExp_mapc_projection f state expression

end Flapjack.Test.CrepHolStateParity
