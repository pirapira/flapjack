import Flapjack.Pancake.Semantics.PanSem.TotalEvalExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite

/-!
# Finite support preserved by the exact panSem clause steps

Towards the exact program evaluator `evaluate_def` over the finite-support state
carrier, this module records that every clause step used by
`evalPanSemNonrecursiveHOLExact` and the recursive dispatcher maps a
finite-support input state to a finite-support output state.

Each step updates only non-map fields (`memory`, `ffi`) or one of the reviewed
map primitives (`setVarHOLExact`, `setGlobalHOLExact`, `setKvarHOLExact`,
`emptyLocalsHOLExact`, `decClockHOLExact`, `fixClockHOLExact`), so field-wise
finite support is preserved. These are Flapjack-specific infrastructure lemmas
(no `@[hol]` tag): HOL states carry `|->` finite maps by construction, so HOL
needs no equivalent statement.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL)

/-- The state-update primitives used by the clause steps preserve finite support. -/
macro "finiteSupport_simp" : tactic =>
  `(tactic|
    (repeat split) <;>
      (first
        | assumption
        | exact PanSemStateExact.finiteSupport_emptyLocals (by assumption)
        | exact PanSemStateExact.finiteSupport_decClock (by assumption)
        | exact PanSemStateExact.finiteSupport_setVar (by assumption) _ _
        | exact PanSemStateExact.finiteSupport_setGlobal (by assumption) _ _
        | exact PanSemStateExact.finiteSupport_setKvar (by assumption) _ _ _
        | exact PanSemStateExact.finiteSupport_fixClock _ _ (by assumption)
        | (simp_all [PanSemStateExact.FiniteSupport,
            PanSemStateExact.finiteSupport_emptyLocals,
            PanSemStateExact.finiteSupport_setVar,
            PanSemStateExact.finiteSupport_setGlobal,
            PanSemStateExact.finiteSupport_setKvar,
            PanSemStateExact.finiteSupport_decClock,
            PanSemStateExact.finiteSupport_fixClock] <;>
          assumption)))

theorem assignStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (assignStepHOLExact state kind name source evalExpression).2.FiniteSupport := by
  unfold assignStepHOLExact
  finiteSupport_simp

theorem primitiveStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (h : state.FiniteSupport) :
    (primitiveStepHOLExact state name operator arguments evalExpressions).2.FiniteSupport := by
  unfold primitiveStepHOLExact
  finiteSupport_simp

theorem storeStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeStepHOLExact state destination source evalExpression).2.FiniteSupport := by
  unfold storeStepHOLExact
  finiteSupport_simp

theorem store32StepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (store32StepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold store32StepHOLExact
  finiteSupport_simp

theorem storeByteStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeByteStepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold storeByteStepHOLExact
  finiteSupport_simp

theorem extCallStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width)
    (h : state.FiniteSupport) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.FiniteSupport := by
  unfold extCallStepHOLExact
  finiteSupport_simp

theorem returnStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (returnStepHOLExact state expression evalExpression).2.FiniteSupport := by
  unfold returnStepHOLExact
  finiteSupport_simp

theorem raiseStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionId : MlS) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (raiseStepHOLExact state exceptionId expression evalExpression).2.FiniteSupport := by
  unfold raiseStepHOLExact
  finiteSupport_simp

theorem shMemLoadHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat)
    (h : state.FiniteSupport) :
    (shMemLoadHOLExact state kind name address nb).2.FiniteSupport := by
  unfold shMemLoadHOLExact
  split
  · split
    · split
      · exact PanSemStateExact.finiteSupport_emptyLocals h
      · simpa [PanSemStateExact.FiniteSupport] using
          PanSemStateExact.finiteSupport_setKvar h kind name _
    · simpa using h
  · split
    · split
      · exact PanSemStateExact.finiteSupport_emptyLocals h
      · simpa [PanSemStateExact.FiniteSupport] using
          PanSemStateExact.finiteSupport_setKvar h kind name _
    · simpa using h

theorem shMemStoreHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (word address : RiscV.Word width) (nb : Nat)
    (h : state.FiniteSupport) :
    (shMemStoreHOLExact state word address nb).2.FiniteSupport := by
  unfold shMemStoreHOLExact
  split
  · split
    · split
      · simpa using h
      · simpa [PanSemStateExact.FiniteSupport] using h
    · simpa using h
  · split
    · split
      · simpa using h
      · simpa [PanSemStateExact.FiniteSupport] using h
    · simpa using h

theorem tickStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (tickStepHOLExact state).2.FiniteSupport := by
  unfold tickStepHOLExact
  split
  · exact PanSemStateExact.finiteSupport_emptyLocals h
  · exact PanSemStateExact.finiteSupport_decClock h

theorem shMemLoadClauseHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS)
    (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.FiniteSupport := by
  unfold shMemLoadClauseHOLExact
  split
  · split
    · exact shMemLoadHOLExact_finiteSupport state kind name _ (nbOpHOL operator) h
    · simpa using h
  · simpa using h

theorem shMemStoreClauseHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.FiniteSupport := by
  unfold shMemStoreClauseHOLExact
  split
  · split
    · exact shMemStoreHOLExact_finiteSupport state _ _ (nbOpHOL operator) h
    · simpa using h
  · simpa using h

/-- Finite support is preserved by the nonrecursive exact dispatcher: whenever
    `evalPanSemNonrecursiveHOLExact` returns a state, that state has finite
    support. `none` (a recursive or not-yet-assembled constructor) carries no
    state and is vacuous. -/
theorem evalPanSemNonrecursiveHOLExact_finiteSupport {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (h : state.FiniteSupport)
    (result : Option (PanSemResultExact width) × PanSemStateExact width σ)
    (hres : evalPanSemNonrecursiveHOLExact program state = some result) :
    result.2.FiniteSupport := by
  cases program with
  | skip =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      simpa using h
  | dec _ _ _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | assign kind name source =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact assignStepHOLExact_finiteSupport state kind name source
        (fun _ expression => evalHOLExact state expression) h
  | primitive name operator arguments =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact primitiveStepHOLExact_finiteSupport state name operator arguments
        (fun _ expressions => evalListHOLExact state expressions) h
  | store address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact storeStepHOLExact_finiteSupport state address value
        (fun _ expression => evalHOLExact state expression) h
  | store32 address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact store32StepHOLExact_finiteSupport state address value
        (fun _ expression => evalHOLExact state expression) h
  | storeByte address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact storeByteStepHOLExact_finiteSupport state address value
        (fun _ expression => evalHOLExact state expression) h
  | seq _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | ite _ _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | «while» _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | «break» =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      simpa using h
  | «continue» =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      simpa using h
  | call _ _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | decCall _ _ _ _ _ => simp [evalPanSemNonrecursiveHOLExact] at hres
  | extCall function configuration configurationLength array arrayLength =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact extCallStepHOLExact_finiteSupport state
        (fun _ expression => evalHOLExact state expression)
        function configuration configurationLength array arrayLength h
  | raise exception value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact raiseStepHOLExact_finiteSupport state exception value
        (fun _ expression => evalHOLExact state expression) h
  | «return» value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact returnStepHOLExact_finiteSupport state value
        (fun _ expression => evalHOLExact state expression) h
  | shMemLoad size kind name address =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact shMemLoadClauseHOLExact_finiteSupport state size kind name address
        (fun _ expression => evalHOLExact state expression) h
  | shMemStore size address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact shMemStoreClauseHOLExact_finiteSupport state size address value
        (fun _ expression => evalHOLExact state expression) h
  | tick =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact tickStepHOLExact_finiteSupport state h
  | annot _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      simpa using h

end Flapjack
