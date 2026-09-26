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

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL ShapeHOL)

/-- The `.state` projection of a context rebuilt by `withState` is the supplied
    state: this is definitional, and lets the recursive preservation proof
    normalize the `withState` wrappers introduced by `fun_induction`. -/
theorem PanSemExactEvalContext.withState_state {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (state : PanSemStateExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) :
    (context.withState state hmem hshared).state = state := rfl

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
    (state : PanSemStateExact width σ) (instMem : DecidablePred state.memaddrs)
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeStepHOLExact state destination source evalExpression).2.FiniteSupport := by
  unfold storeStepHOLExact
  finiteSupport_simp

theorem store32StepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (instMem : DecidablePred state.memaddrs)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (store32StepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold store32StepHOLExact
  finiteSupport_simp

theorem storeByteStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (instMem : DecidablePred state.memaddrs)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeByteStepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold storeByteStepHOLExact
  finiteSupport_simp

theorem extCallStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (instMem : DecidablePred state.memaddrs)
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
    (state : PanSemStateExact width σ) (instSh : DecidablePred state.shMemaddrs)
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
    (state : PanSemStateExact width σ) (instSh : DecidablePred state.shMemaddrs)
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
    (state : PanSemStateExact width σ) (instSh : DecidablePred state.shMemaddrs)
    (operator : OpSize) (kind : VarKind) (name : MlS)
    (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.FiniteSupport := by
  unfold shMemLoadClauseHOLExact
  split
  · split
    · exact shMemLoadHOLExact_finiteSupport state instSh kind name _ (nbOpHOL operator) h
    · simpa using h
  · simpa using h

theorem shMemStoreClauseHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (instSh : DecidablePred state.shMemaddrs)
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.FiniteSupport := by
  unfold shMemStoreClauseHOLExact
  split
  · split
    · exact shMemStoreHOLExact_finiteSupport state instSh _ _ (nbOpHOL operator) h
    · simpa using h
  · simpa using h

/-- Finite support is preserved by the nonrecursive exact dispatcher: whenever
    `evalPanSemNonrecursiveHOLExact` returns a state, that state has finite
    support. `none` (a recursive or not-yet-assembled constructor) carries no
    state and is vacuous. -/
theorem evalPanSemNonrecursiveHOLExact_finiteSupport {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    (instMem : DecidablePred state.memaddrs) (instSh : DecidablePred state.shMemaddrs)
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
      exact storeStepHOLExact_finiteSupport state instMem address value
        (fun _ expression => evalHOLExact state expression) h
  | store32 address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact store32StepHOLExact_finiteSupport state instMem address value
        (fun _ expression => evalHOLExact state expression) h
  | storeByte address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact storeByteStepHOLExact_finiteSupport state instMem address value
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
      exact extCallStepHOLExact_finiteSupport state instMem
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
      exact shMemLoadClauseHOLExact_finiteSupport state instSh size kind name address
        (fun _ expression => evalHOLExact state expression) h
  | shMemStore size address value =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact shMemStoreClauseHOLExact_finiteSupport state instSh size address value
        (fun _ expression => evalHOLExact state expression) h
  | tick =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      exact tickStepHOLExact_finiteSupport state h
  | annot _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq] at hres
      rw [← hres]
      simpa using h

/-! ## Finite support helpers for the recursive evaluator

The recursive dispatcher builds locals maps with `List.foldl` (the Zipped
`lookup_code` locals) and restores a caller binding with `resVarHOLExact`, and
changes only `clock`/`locals` fields. The lemmas below record finite support for
those constructions, so the recursive preservation induction can reuse the
clause-step lemmas above. -/

/-- The Zipped `lookup_code` locals fold keeps an explicit finite support: the
    keys of the produced map are among the entries' first components. -/
theorem foldl_set_finiteSupport {α β : Type} [DecidableEq α] (entries : List (α × β))
    (init : α → Option β)
    (hinit : ∃ keys : List α, ∀ key, init key ≠ none → key ∈ keys) :
    ∃ keys : List α,
      ∀ key, (entries.foldl
        (fun (map : α → Option β) (entry : α × β) =>
          fun current => if current = entry.1 then some entry.2 else map current)
        init) key ≠ none → key ∈ keys := by
  induction entries generalizing init with
  | nil => exact hinit
  | cons entry entries ih =>
      apply ih
      obtain ⟨keys, hkeys⟩ := hinit
      refine ⟨entry.1 :: keys, ?_⟩
      intro key hk
      by_cases h : key = entry.1
      · subst h
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        apply hkeys
        simpa [h] using hk

/-- The function-backed `res_var` keeps finite support (delete or update). -/
theorem resVarHOLExact_finiteSupport {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width)) (entry : MlS × Option (ValueHOL width))
    (hl : ∃ keys : List MlS, ∀ key, locals key ≠ none → key ∈ keys) :
    ∃ keys : List MlS, ∀ key, resVarHOLExact locals entry key ≠ none → key ∈ keys := by
  obtain ⟨keys, hkeys⟩ := hl
  refine ⟨entry.1 :: keys, ?_⟩
  intro key hk
  obtain ⟨name, valueOpt⟩ := entry
  cases valueOpt with
  | none =>
      simp only [resVarHOLExact] at hk
      by_cases h : key = name
      · subst h
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        apply hkeys
        simpa [h] using hk
  | some value =>
      simp only [resVarHOLExact] at hk
      by_cases h : key = name
      · subst h
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        apply hkeys
        simpa [h] using hk

/-- Replacing the locals field with a finite-support function keeps the state
    finite-support. -/
theorem PanSemStateExact.finiteSupport_setLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (locals : MlS → Option (ValueHOL width))
    (hl : ∃ keys : List MlS, ∀ key, locals key ≠ none → key ∈ keys)
    (h : state.FiniteSupport) :
    ({ state with locals := locals } : PanSemStateExact width σ).FiniteSupport := by
  obtain ⟨_, hg, hc, he⟩ := h
  exact ⟨hl, hg, hc, he⟩

/-- Changing only the clock keeps finite support. -/
theorem PanSemStateExact.finiteSupport_setClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (clock : Nat) (h : state.FiniteSupport) :
    ({ state with clock := clock } : PanSemStateExact width σ).FiniteSupport := by
  simpa [PanSemStateExact.FiniteSupport] using h

/-- The Zipped `lookup_code` locals map has finite support. -/
theorem lookupCodeHOLExact_calleeLocals_finiteSupport {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (arguments : List (ValueHOL width))
    (body : ProgHOL width) (calleeLocals : MlS → Option (ValueHOL width))
    (returnShape : ShapeHOL)
    (h : lookupCodeHOLExact code fname arguments = some (body, calleeLocals, returnShape)) :
    ∃ keys : List MlS, ∀ key, calleeLocals key ≠ none → key ∈ keys := by
  unfold lookupCodeHOLExact at h
  split at h
  · exact absurd h (by simp)
  · rename_i parameters body' returnShape' heq
    by_cases hcond : (parameters.map Prod.fst).Nodup ∧
        parameters.length = arguments.length ∧
        ((parameters.zip arguments).all
          (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
    · rw [if_pos hcond] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hlocals, _⟩ := h
      subst hlocals
      exact foldl_set_finiteSupport _ _
        ⟨[], by intro key hk; exact absurd rfl hk⟩
    · rw [if_neg hcond] at h
      exact absurd h (by simp)

end Flapjack
