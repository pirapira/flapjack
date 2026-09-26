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

/-- An exact evaluation context is determined by its state; the two
    `DecidablePred` fields are proof-irrelevant for the respective predicates.
    Lets proofs compare `withState` call sites without unfolding their proof
    terms. -/
theorem PanSemExactEvalContext.ext {width : Nat} {σ : Type} [NeZero width]
    {c1 c2 : PanSemExactEvalContext width σ} (h : c1.state = c2.state) : c1 = c2 := by
  cases c1 with
  | mk s1 m1 sh1 =>
  cases c2 with
  | mk s2 m2 sh2 =>
  dsimp only at h
  subst h
  congr
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

instance {width : Nat} {σ : Type} [NeZero width] (context : PanSemExactEvalContext width σ) :
    DecidablePred context.state.memaddrs := context.memaddrsDecidable

instance {width : Nat} {σ : Type} [NeZero width] (context : PanSemExactEvalContext width σ) :
    DecidablePred context.state.shMemaddrs := context.shMemaddrsDecidable

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
    (state : PanSemStateExact width σ) [instMem : DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeStepHOLExact state destination source evalExpression).2.FiniteSupport := by
  unfold storeStepHOLExact
  finiteSupport_simp

theorem store32StepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [instMem : DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (store32StepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold store32StepHOLExact
  finiteSupport_simp

theorem storeByteStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [instMem : DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (h : state.FiniteSupport) :
    (storeByteStepHOLExact state address value evalExpression).2.FiniteSupport := by
  unfold storeByteStepHOLExact
  finiteSupport_simp

theorem extCallStepHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [instMem : DecidablePred state.memaddrs]
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
    (state : PanSemStateExact width σ) [instSh : DecidablePred state.shMemaddrs]
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
    (state : PanSemStateExact width σ) [instSh : DecidablePred state.shMemaddrs]
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
    (state : PanSemStateExact width σ) [instSh : DecidablePred state.shMemaddrs]
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
    (state : PanSemStateExact width σ) [instSh : DecidablePred state.shMemaddrs]
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
    [instMem : DecidablePred state.memaddrs] [instSh : DecidablePred state.shMemaddrs]
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

/-- The recursive `Call` branch builds its entry state by replacing `locals`
    with the `Zipped` callee locals and decrementing `clock`. Only the map
    fields `locals`/`globals`/`code`/`eshapes` matter for finite support, so the
    entry state is finite-support whenever the caller state is and the callee
    locals have finite support. -/
theorem PanSemStateExact.finiteSupport_setLocals_clock {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    (locals : MlS → Option (ValueHOL width)) (clock : Nat)
    (hl : ∃ keys : List MlS, ∀ key, locals key ≠ none → key ∈ keys)
    (h : state.FiniteSupport) :
    ({ state with locals := locals, clock := clock } : PanSemStateExact width σ).FiniteSupport := by
  obtain ⟨_, hg, hc, he⟩ := h
  exact ⟨hl, hg, hc, he⟩

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

/-! ### Per-constructor recursive cases of finite-support preservation

The correctness target `evalPanSemRecursiveCallContextHOLExact_finiteSupport` is
proved by the well-founded induction generated by the evaluator's own
termination measure `(context.state.clock, sizeOf program)`. The following
lemmas expose one recursive constructor at a time and take the induction
hypothesis for each recursive sub-call as an explicit hypothesis, so the final
induction only has to discharge those hypotheses. This is Flapjack-specific
infrastructure: the evaluator is not a tagged HOL port. -/

/-- Recursive `Dec` case of finite-support preservation, parameterized by the
    induction hypothesis for the body. -/
theorem evalPanSemRecursiveCallContextHOLExact_dec_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (ih : ∀ (bodyContext : PanSemExactEvalContext width σ),
        bodyContext.state.FiniteSupport →
        ∀ result, evalPanSemRecursiveCallContextHOLExact body bodyContext = some result →
          result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.dec name shape initializer body) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  cases hval : evalHOLExact context.state initializer with
  | none =>
      simp only [hval, Option.some.injEq] at hres
      rw [← hres]
      exact h
  | some value =>
      simp only [hval] at hres
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · rw [if_pos hshape] at hres
        cases hrec : evalPanSemRecursiveCallContextHOLExact body
            (context.withState (setVarHOLExact name value context.state) rfl rfl) with
        | none => simp only [hrec] at hres; cases hres
        | some res =>
            simp only [hrec] at hres
            obtain ⟨r, postContext⟩ := res
            simp only [Option.some.injEq] at hres
            obtain ⟨hr, rfl⟩ := hres
            have hbody : (context.withState (setVarHOLExact name value context.state) rfl rfl).state.FiniteSupport := by
              change (setVarHOLExact name value context.state).FiniteSupport
              exact PanSemStateExact.finiteSupport_setVar h name value
            have hpost : postContext.state.FiniteSupport := ih _ hbody (r, postContext) hrec
            have hl' := resVarHOLExact_finiteSupport postContext.state.locals
              (name, context.state.locals name) hpost.1
            exact PanSemStateExact.finiteSupport_setLocals postContext.state
              (resVarHOLExact postContext.state.locals (name, context.state.locals name))
              hl' hpost
      · rw [if_neg hshape] at hres
        simp only [Option.some.injEq] at hres
        rw [← hres]
        exact h

/-- Recursive `Seq` case of finite-support preservation, parameterized by the
    induction hypotheses for the first and second sub-evaluations. -/
theorem evalPanSemRecursiveCallContextHOLExact_seq_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width)
    (context : PanSemExactEvalContext width σ) (_h : context.state.FiniteSupport)
    (ihFirst : ∀ result,
        evalPanSemRecursiveCallContextHOLExact first context = some result →
          result.2.state.FiniteSupport)
    (ihSecond : ∀ (fixedContext : PanSemExactEvalContext width σ),
        fixedContext.state.FiniteSupport →
        ∀ result, evalPanSemRecursiveCallContextHOLExact second fixedContext = some result →
          result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.seq first second) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  cases hfirst : evalPanSemRecursiveCallContextHOLExact first context with
  | none => simp only [hfirst] at hres; cases hres
  | some pair =>
      obtain ⟨firstResult, firstContext⟩ := pair
      simp only [hfirst] at hres
      cases firstResult with
      | none =>
          simp only at hres
          have hfix : (firstContext.withState
              (fixClockHOLExact context.state
                ((none : Option (PanSemResultExact width)), firstContext.state)).2 rfl rfl).state.FiniteSupport := by
            change (fixClockHOLExact context.state
              ((none : Option (PanSemResultExact width)), firstContext.state)).2.FiniteSupport
            exact PanSemStateExact.finiteSupport_fixClock context.state
              ((none : Option (PanSemResultExact width)), firstContext.state)
              (ihFirst (none, firstContext) hfirst)
          exact ihSecond _ hfix result hres
      | some r =>
          simp only at hres
          simp only [Option.some.injEq] at hres
          cases result with
          | mk r' ctx' =>
              simp only [Prod.mk.injEq] at hres
              obtain ⟨_, h2⟩ := hres
              rw [← h2]
              change (fixClockHOLExact context.state (some r, firstContext.state)).2.FiniteSupport
              exact PanSemStateExact.finiteSupport_fixClock context.state (some r, firstContext.state)
                (ihFirst (some r, firstContext) hfirst)

/-- Recursive `Ite` case of finite-support preservation, parameterized by the
    induction hypotheses for the two branches (both evaluated in the same
    context). -/
theorem evalPanSemRecursiveCallContextHOLExact_ite_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (ihThen : ∀ result,
        evalPanSemRecursiveCallContextHOLExact thenBranch context = some result →
          result.2.state.FiniteSupport)
    (ihElse : ∀ result,
        evalPanSemRecursiveCallContextHOLExact elseBranch context = some result →
          result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.ite condition thenBranch elseBranch) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  cases hcond : evalHOLExact context.state condition with
  | none =>
      simp only [hcond] at hres
      simp only [Option.some.injEq] at hres
      rw [← hres]
      exact h
  | some v =>
      simp only [hcond] at hres
      cases v with
      | val wordLab =>
          cases wordLab with
          | word value =>
              simp only at hres
              by_cases hz : (value != 0) = true
              · rw [if_pos hz] at hres
                exact ihThen result hres
              · rw [if_neg hz] at hres
                exact ihElse result hres
      | rStruct fields =>
          simp only [Option.some.injEq] at hres
          rw [← hres]
          exact h
      | nStruct name fields =>
          simp only [Option.some.injEq] at hres
          rw [← hres]
          exact h

/-- Recursive `While` case with the condition already evaluated to a nonzero
    word, parameterized by the body and self induction hypotheses. -/
theorem evalPanSemRecursiveCallContextHOLExact_whileWord_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (word : BitVec width)
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (hcond : evalHOLExact context.state condition = some (.val (.word word)))
    (hw : word ≠ 0)
    (ihBody : ∀ (bodyContext : PanSemExactEvalContext width σ),
        bodyContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact body bodyContext = some result →
            result.2.state.FiniteSupport)
    (ihSelf : ∀ (selfContext : PanSemExactEvalContext width σ),
        selfContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact (.while condition body) selfContext = some result →
            result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.while condition body) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  simp only [hcond] at hres
  rw [if_pos hw] at hres
  by_cases hclock : context.state.clock = 0
  · rw [if_pos hclock] at hres
    simp only [Option.some.injEq] at hres
    rw [← hres]
    change (emptyLocalsHOLExact context.state).FiniteSupport
    exact PanSemStateExact.finiteSupport_emptyLocals h
  · rw [if_neg hclock] at hres
    cases hbody : evalPanSemRecursiveCallContextHOLExact body
        (context.withState (decClockHOLExact context.state) rfl rfl) with
    | none => simp only [hbody] at hres; cases hres
    | some res =>
        simp only [hbody] at hres
        obtain ⟨bodyResult, bodyContext⟩ := res
        have hbodyfs : bodyContext.state.FiniteSupport :=
          ihBody _ (by
            change (decClockHOLExact context.state).FiniteSupport
            exact PanSemStateExact.finiteSupport_decClock h)
            (bodyResult, bodyContext) hbody
        have hfixed : (bodyContext.withState
            (fixClockHOLExact (decClockHOLExact context.state)
              (bodyResult, bodyContext.state)).2 rfl rfl).state.FiniteSupport := by
          change (fixClockHOLExact (decClockHOLExact context.state)
            (bodyResult, bodyContext.state)).2.FiniteSupport
          exact PanSemStateExact.finiteSupport_fixClock (decClockHOLExact context.state)
            (bodyResult, bodyContext.state) hbodyfs
        cases bodyResult with
        | none => simp only at hres; exact ihSelf _ hfixed result hres
        | some r =>
            cases r with
            | «continue» => simp only at hres; exact ihSelf _ hfixed result hres
            | «break» =>
                simp only at hres
                simp only [Option.some.injEq] at hres
                obtain ⟨_, rfl⟩ := hres
                exact hfixed
            | error => simp only at hres; obtain ⟨_, rfl⟩ := hres; exact hfixed
            | timeOut => simp only at hres; obtain ⟨_, rfl⟩ := hres; exact hfixed
            | returned value => simp only at hres; obtain ⟨_, rfl⟩ := hres; exact hfixed
            | exception exceptionId value =>
                simp only at hres; obtain ⟨_, rfl⟩ := hres; exact hfixed
            | finalFfi event => simp only at hres; obtain ⟨_, rfl⟩ := hres; exact hfixed

/-- Recursive `While` case of finite-support preservation, parameterized by the
    induction hypothesis for the body and the self induction hypothesis for the
    loop (evaluated with a smaller clock). -/
theorem evalPanSemRecursiveCallContextHOLExact_while_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width)
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (ihBody : ∀ (bodyContext : PanSemExactEvalContext width σ),
        bodyContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact body bodyContext = some result →
            result.2.state.FiniteSupport)
    (ihSelf : ∀ (selfContext : PanSemExactEvalContext width σ),
        selfContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact (.while condition body) selfContext = some result →
            result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.while condition body) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  cases hcond : evalHOLExact context.state condition with
  | none =>
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
      simp only [hcond] at hres
      simp only [Option.some.injEq] at hres
      rw [← hres]
      exact h
  | some v =>
      cases v with
      | val wordLab =>
          cases wordLab with
          | word word =>
              by_cases hw : word ≠ 0
              · exact evalPanSemRecursiveCallContextHOLExact_whileWord_finiteSupport
                  condition body word context h hcond hw ihBody ihSelf result hres
              · rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
                simp only [hcond] at hres
                rw [if_neg hw] at hres
                simp only [Option.some.injEq] at hres
                obtain ⟨_, rfl⟩ := hres
                exact h
      | rStruct fields =>
          rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
          simp only [hcond] at hres
          simp only [Option.some.injEq] at hres
          rw [← hres]
          exact h
      | nStruct name fields =>
          rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
          simp only [hcond] at hres
          simp only [Option.some.injEq] at hres
          rw [← hres]
          exact h


theorem evalPanSemRecursiveCallContextHOLExact_call_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (ihBody : ∀ (body : ProgHOL width) (entryContext : PanSemExactEvalContext width σ),
        entryContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact body entryContext = some result →
            result.2.state.FiniteSupport)
    (ihHandler : ∀ (handlerProgram : ProgHOL width)
        (handlerContext : PanSemExactEvalContext width σ),
        handlerContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact handlerProgram handlerContext = some result →
            result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact (.call info function arguments) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  cases hargs : evalListHOLExact context.state arguments with
  | none =>
      simp only [hargs, Option.some.injEq] at hres
      rw [← hres]
      exact h
  | some values =>
      simp only [hargs] at hres
      cases hlookup : lookupCodeHOLExact context.state.code function values with
      | none =>
          simp only [hlookup, Option.some.injEq] at hres
          rw [← hres]
          exact h
      | some triple =>
          obtain ⟨body, calleeLocals, returnShape⟩ := triple
          simp only [hlookup] at hres
          by_cases hclock : context.state.clock = 0
          · rw [if_pos hclock] at hres
            simp only [Option.some.injEq] at hres
            rw [← hres]
            exact PanSemStateExact.finiteSupport_emptyLocals h
          · rw [if_neg hclock] at hres
            have hentry : (callEntryStateHOLExact context.state calleeLocals).FiniteSupport :=
              PanSemStateExact.finiteSupport_setLocals_clock context.state calleeLocals
                (context.state.clock - 1)
                (lookupCodeHOLExact_calleeLocals_finiteSupport context.state.code function
                  values body calleeLocals returnShape hlookup) h
            cases hbody : evalPanSemRecursiveCallContextHOLExact body
                (context.withState (callEntryStateHOLExact context.state calleeLocals) rfl rfl) with
            | none => simp only [hbody] at hres; cases hres
            | some pair =>
                obtain ⟨bodyResult, bodyContext⟩ := pair
                simp only [hbody] at hres
                have hbodyfs : bodyContext.state.FiniteSupport :=
                  ihBody body
                    (context.withState (callEntryStateHOLExact context.state calleeLocals) rfl rfl)
                    (by exact hentry)
                    (bodyResult, bodyContext) hbody
                have hfixed : (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (bodyResult, bodyContext.state)).2.FiniteSupport :=
                  PanSemStateExact.finiteSupport_fixClock _ _ hbodyfs
                let fixedCtx : PanSemExactEvalContext width σ := bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (bodyResult, bodyContext.state)).snd rfl rfl
                have hfixedCtx : fixedCtx.state.FiniteSupport := hfixed
                cases bodyResult with
                | none =>
                    simp only [Option.some.injEq] at hres
                    rw [← hres]
                    exact hfixedCtx
                | some r =>
                    cases r with
                    | «error» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «timeOut» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «break» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact hfixedCtx
                    | «continue» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact hfixedCtx
                    | «returned» value =>
                        try (simp only at hres)
                        by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
                        · rw [if_pos hshape] at hres
                          cases hinfo : info with
                          | none =>
                              simp only [hinfo, Option.some.injEq] at hres
                              rw [← hres]
                              exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                          | some inner =>
                              simp only [hinfo] at hres
                              rcases inner with ⟨returns, handler⟩
                              cases returns with
                              | none =>
                                  try (simp only at hres)
                                  simp only [Option.some.injEq] at hres
                                  rw [← hres]
                                  change ({ fixedCtx.state with locals := context.state.locals } : PanSemStateExact width σ).FiniteSupport
                                  exact PanSemStateExact.finiteSupport_setLocals fixedCtx.state context.state.locals h.1 hfixedCtx
                              | some kn =>
                                  rcases kn with ⟨kind, name⟩
                                  try (simp only at hres)
                                  by_cases hvalid : isValidValueHOLExact context.state kind name value = true
                                  · rw [if_pos hvalid] at hres
                                    simp only [Option.some.injEq] at hres
                                    rw [← hres]
                                    change (setKvarHOLExact kind name value ({ fixedCtx.state with locals := context.state.locals } : PanSemStateExact width σ)).FiniteSupport
                                    exact PanSemStateExact.finiteSupport_setKvar (PanSemStateExact.finiteSupport_setLocals fixedCtx.state context.state.locals h.1 hfixedCtx) kind name value
                                  · rw [if_neg hvalid] at hres
                                    simp only [Option.some.injEq] at hres
                                    rw [← hres]
                                    exact hfixedCtx
                        · rw [if_neg hshape] at hres
                          simp only [Option.some.injEq] at hres
                          rw [← hres]
                          exact hfixedCtx
                    | «exception» exceptionId value =>
                        try (simp only at hres)
                        cases hinfo : info with
                        | none =>
                            simp only [hinfo, Option.some.injEq] at hres
                            rw [← hres]
                            exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                        | some inner =>
                            simp only [hinfo] at hres
                            rcases inner with ⟨returns, handler⟩
                            cases handler with
                            | none =>
                                try (simp only at hres)
                                simp only [Option.some.injEq] at hres
                                rw [← hres]
                                exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                            | some htriple =>
                                rcases htriple with ⟨handlerId, handlerVar, handlerProgram⟩
                                try (simp only at hres)
                                by_cases heq : exceptionId = handlerId
                                · rw [if_pos heq] at hres
                                  cases heshapes : context.state.eshapes exceptionId with
                                  | none =>
                                      simp only [heshapes, Option.some.injEq] at hres
                                      rw [← hres]
                                      exact hfixedCtx
                                  | some shape =>
                                      simp only [heshapes] at hres
                                      by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) shape && isValidValueHOLExact context.state .local handlerVar value) = true
                                      · rw [if_pos hcond] at hres
                                        have hhandler : (fixedCtx.withState (setVarHOLExact handlerVar value ({ fixedCtx.state with locals := context.state.locals } : PanSemStateExact width σ)) rfl rfl).state.FiniteSupport := by
                                          change (setVarHOLExact handlerVar value ({ fixedCtx.state with locals := context.state.locals } : PanSemStateExact width σ)).FiniteSupport
                                          exact PanSemStateExact.finiteSupport_setVar (PanSemStateExact.finiteSupport_setLocals fixedCtx.state context.state.locals h.1 hfixedCtx) handlerVar value
                                        exact ihHandler handlerProgram (fixedCtx.withState (setVarHOLExact handlerVar value ({ fixedCtx.state with locals := context.state.locals } : PanSemStateExact width σ)) rfl rfl) hhandler result hres
                                      · rw [if_neg hcond] at hres
                                        simp only [Option.some.injEq] at hres
                                        rw [← hres]
                                        exact hfixedCtx
                                · rw [if_neg heq] at hres
                                  simp only [Option.some.injEq] at hres
                                  rw [← hres]
                                  exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «finalFfi» event =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx


theorem evalPanSemRecursiveCallContextHOLExact_decCall_finiteSupport
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : PanSemExactEvalContext width σ) (h : context.state.FiniteSupport)
    (ihBody : ∀ (body : ProgHOL width) (entryContext : PanSemExactEvalContext width σ),
        entryContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact body entryContext = some result →
            result.2.state.FiniteSupport)
    (ihContinuation : ∀ (continuationContext : PanSemExactEvalContext width σ),
        continuationContext.state.FiniteSupport →
        ∀ result,
          evalPanSemRecursiveCallContextHOLExact continuation continuationContext = some result →
            result.2.state.FiniteSupport) :
    ∀ result,
      evalPanSemRecursiveCallContextHOLExact
        (.decCall resultName shape function arguments continuation) context = some result →
        result.2.state.FiniteSupport := by
  intro result hres
  rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hres
  cases hargs : evalListHOLExact context.state arguments with
  | none =>
      simp only [hargs, Option.some.injEq] at hres
      rw [← hres]
      exact h
  | some values =>
      simp only [hargs] at hres
      cases hlookup : lookupCodeHOLExact context.state.code function values with
      | none =>
          simp only [hlookup, Option.some.injEq] at hres
          rw [← hres]
          exact h
      | some triple =>
          obtain ⟨body, calleeLocals, returnShape⟩ := triple
          simp only [hlookup] at hres
          by_cases hclock : context.state.clock = 0
          · rw [if_pos hclock] at hres
            simp only [Option.some.injEq] at hres
            rw [← hres]
            exact PanSemStateExact.finiteSupport_emptyLocals h
          · rw [if_neg hclock] at hres
            have hentry : (callEntryStateHOLExact context.state calleeLocals).FiniteSupport :=
              PanSemStateExact.finiteSupport_setLocals_clock context.state calleeLocals
                (context.state.clock - 1)
                (lookupCodeHOLExact_calleeLocals_finiteSupport context.state.code function
                  values body calleeLocals returnShape hlookup) h
            cases hbody : evalPanSemRecursiveCallContextHOLExact body
                (context.withState (callEntryStateHOLExact context.state calleeLocals) rfl rfl) with
            | none => simp only [hbody] at hres; cases hres
            | some pair =>
                obtain ⟨bodyResult, bodyContext⟩ := pair
                simp only [hbody] at hres
                have hbodyfs : bodyContext.state.FiniteSupport :=
                  ihBody body
                    (context.withState (callEntryStateHOLExact context.state calleeLocals) rfl rfl)
                    (by exact hentry)
                    (bodyResult, bodyContext) hbody
                have hfixed : (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (bodyResult, bodyContext.state)).2.FiniteSupport :=
                  PanSemStateExact.finiteSupport_fixClock _ _ hbodyfs
                let fixedCtx : PanSemExactEvalContext width σ := bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (bodyResult, bodyContext.state)).snd rfl rfl
                have hfixedCtx : fixedCtx.state.FiniteSupport := hfixed
                cases bodyResult with
                | none =>
                    simp only [Option.some.injEq] at hres
                    rw [← hres]
                    exact hfixedCtx
                | some r =>
                    cases r with
                    | «error» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «timeOut» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «break» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact hfixedCtx
                    | «continue» =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact hfixedCtx
                    | «returned» value =>
                        try (simp only at hres)
                        by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape) = true
                        · rw [if_pos hcond] at hres
                          cases hcont : evalPanSemRecursiveCallContextHOLExact continuation
                              ((bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (some (PanSemResultExact.returned value), bodyContext.state)).snd rfl rfl).withState (setVarHOLExact resultName value ({ (bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (some (PanSemResultExact.returned value), bodyContext.state)).snd rfl rfl).state with locals := context.state.locals } : PanSemStateExact width σ)) rfl rfl) with
                          | none => try (simp only [hcont] at hres); cases hres
                          | some cpair =>
                              obtain ⟨continuationResult, continuationPost⟩ := cpair
                              try (simp only [hcont] at hres)
                              have hcontEntry : ((bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (some (PanSemResultExact.returned value), bodyContext.state)).snd rfl rfl).withState (setVarHOLExact resultName value ({ (bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (some (PanSemResultExact.returned value), bodyContext.state)).snd rfl rfl).state with locals := context.state.locals } : PanSemStateExact width σ)) rfl rfl).state.FiniteSupport := by
                                change (setVarHOLExact resultName value ({ (bodyContext.withState (fixClockHOLExact (callEntryStateHOLExact context.state calleeLocals) (some (PanSemResultExact.returned value), bodyContext.state)).snd rfl rfl).state with locals := context.state.locals } : PanSemStateExact width σ)).FiniteSupport
                                exact PanSemStateExact.finiteSupport_setVar (PanSemStateExact.finiteSupport_setLocals fixedCtx.state context.state.locals h.1 hfixedCtx) resultName value
                              have hcontF : continuationPost.state.FiniteSupport :=
                                ihContinuation _ hcontEntry (continuationResult, continuationPost) hcont
                              simp only [Option.some.injEq] at hres
                              rw [← hres]
                              change ({ continuationPost.state with locals := resVarHOLExact continuationPost.state.locals (resultName, context.state.locals resultName) } : PanSemStateExact width σ).FiniteSupport
                              exact ⟨resVarHOLExact_finiteSupport continuationPost.state.locals (resultName, context.state.locals resultName) hcontF.1, hcontF.2.1, hcontF.2.2.1, hcontF.2.2.2⟩
                        · rw [if_neg hcond] at hres
                          simp only [Option.some.injEq] at hres
                          rw [← hres]
                          exact hfixedCtx
                    | «exception» exceptionId value =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx
                    | «finalFfi» event =>
                        try (simp only at hres)
                        simp only [Option.some.injEq] at hres
                        rw [← hres]
                        exact PanSemStateExact.finiteSupport_emptyLocals hfixedCtx

/-- Finite-support of the exact `Call`/`DecCall` entry state, whose `locals` are
    replaced by the callee locals and whose `clock` is decremented. -/
theorem callEntryHOLExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (calleeLocals : MlS → Option (ValueHOL width))
    (function : MlS) (values : List (ValueHOL width)) (body : ProgHOL width)
    (returnShape : ShapeHOL)
    (hlookup : lookupCodeHOLExact state.code function values = some (body, calleeLocals, returnShape))
    (h : state.FiniteSupport) :
    ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport :=
  PanSemStateExact.finiteSupport_setLocals_clock state calleeLocals (state.clock - 1)
    (lookupCodeHOLExact_calleeLocals_finiteSupport state.code function values body calleeLocals
      returnShape hlookup) h

macro "closeCase" : tactic => `(tactic|
  (intro result hres) <;> (try (simp only [Option.some.injEq] at hres)) <;> (try (cases hres)) <;>
  (try (dsimp (config := { zetaDelta := true }))) <;>
  (try (dsimp only [PanSemExactEvalContext.withState])) <;>
  (first
    | assumption
    | (apply_assumption <;> assumption)
    | (apply assignStepHOLExact_finiteSupport <;> assumption)
    | (apply primitiveStepHOLExact_finiteSupport <;> assumption)
    | (apply storeStepHOLExact_finiteSupport <;> assumption)
    | (apply store32StepHOLExact_finiteSupport <;> assumption)
    | (apply storeByteStepHOLExact_finiteSupport <;> assumption)
    | (apply extCallStepHOLExact_finiteSupport <;> assumption)
    | (apply returnStepHOLExact_finiteSupport <;> assumption)
    | (apply raiseStepHOLExact_finiteSupport <;> assumption)
    | (apply shMemLoadClauseHOLExact_finiteSupport <;> assumption)
    | (apply shMemStoreClauseHOLExact_finiteSupport <;> assumption)
    | (apply tickStepHOLExact_finiteSupport <;> assumption)
    | (apply evalPanSemNonrecursiveHOLExact_finiteSupport <;> assumption)
    | (apply PanSemStateExact.finiteSupport_emptyLocals; apply PanSemStateExact.finiteSupport_fixClock; assumption)
    | (apply PanSemStateExact.finiteSupport_emptyLocals; apply PanSemStateExact.finiteSupport_decClock; assumption)
    | (apply PanSemStateExact.finiteSupport_emptyLocals; assumption)
    | (apply PanSemStateExact.finiteSupport_fixClock; assumption)
    | (apply PanSemStateExact.finiteSupport_decClock; assumption)
    | exact PanSemStateExact.finiteSupport_setVar (by assumption) _ _
    | exact PanSemStateExact.finiteSupport_setGlobal (by assumption) _ _
    | exact PanSemStateExact.finiteSupport_setKvar (by assumption) _ _ _
    | exact PanSemStateExact.finiteSupport_setLocals (by assumption) _ _
    | exact PanSemStateExact.finiteSupport_setClock (by assumption) _ _
    | exact resVarHOLExact_finiteSupport _ (by assumption) _))

/-- Finite support is preserved by the exact recursive panSem program evaluator. -/
theorem evalPanSemRecursiveCallContextHOLExact_finiteSupport {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (context : PanSemExactEvalContext width σ)
    (h : context.state.FiniteSupport) :
    ∀ result, evalPanSemRecursiveCallContextHOLExact program context = some result →
      result.2.state.FiniteSupport := by
  fun_induction evalPanSemRecursiveCallContextHOLExact program context
  case case3 =>
      rename_i inst context state name shape initializer body value hval hshape bodyState bodyContext
        result postContext hrec restored ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hbody : bodyContext.state.FiniteSupport := by
        change (setVarHOLExact name value state).FiniteSupport
        exact PanSemStateExact.finiteSupport_setVar h name value
      have hpost : postContext.state.FiniteSupport := ih1 hbody (result, postContext) hrec
      have hl' := resVarHOLExact_finiteSupport postContext.state.locals
        (name, state.locals name) hpost.1
      exact PanSemStateExact.finiteSupport_setLocals postContext.state
        (resVarHOLExact postContext.state.locals (name, state.locals name)) hl' hpost
  case case6 =>
      rename_i inst context state first second postContext hfirst fixed fixedContext ih2 ih1
      intro result hres
      have hfix : fixedContext.state.FiniteSupport := by
        change (fixClockHOLExact state ((none : Option (PanSemResultExact width)), postContext.state)).snd.FiniteSupport
        exact PanSemStateExact.finiteSupport_fixClock state
          ((none : Option (PanSemResultExact width)), postContext.state)
          (ih2 h (none, postContext) hfirst)
      exact ih1 hfix result hres
  case case7 =>
      rename_i inst context state first second postContext val hfirst fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      change (fixClockHOLExact state (some val, postContext.state)).snd.FiniteSupport
      exact PanSemStateExact.finiteSupport_fixClock state (some val, postContext.state)
        (ih1 h (some val, postContext) hfirst)
  case case13 =>
      rename_i inst context state condition body value hcond hw hclock entry entryContext
        postContext hbody fixed fixedContext ih2 ih1
      intro result hres
      have hentry : entryContext.state.FiniteSupport := by
        change (decClockHOLExact state).FiniteSupport
        exact PanSemStateExact.finiteSupport_decClock h
      have hfix : fixedContext.state.FiniteSupport := by
        change (fixClockHOLExact entry (some PanSemResultExact.continue, postContext.state)).snd.FiniteSupport
        exact PanSemStateExact.finiteSupport_fixClock entry
          (some PanSemResultExact.continue, postContext.state)
          (ih2 hentry (some PanSemResultExact.continue, postContext) hbody)
      exact ih1 hfix result hres
  case case14 =>
      rename_i inst context state condition body value hcond hw hclock entry entryContext
        postContext hbody fixed fixedContext ih2 ih1
      intro result hres
      have hentry : entryContext.state.FiniteSupport := by
        change (decClockHOLExact state).FiniteSupport
        exact PanSemStateExact.finiteSupport_decClock h
      have hfix : fixedContext.state.FiniteSupport := by
        change (fixClockHOLExact entry ((none : Option (PanSemResultExact width)), postContext.state)).snd.FiniteSupport
        exact PanSemStateExact.finiteSupport_fixClock entry
          ((none : Option (PanSemResultExact width)), postContext.state)
          (ih2 hentry (none, postContext) hbody)
      exact ih1 hfix result hres
  case case15 =>
      rename_i inst context state condition body value hcond hw hclock entry entryContext
        postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change (decClockHOLExact state).FiniteSupport
        exact PanSemStateExact.finiteSupport_decClock h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some PanSemResultExact.break, postContext.state)
        (ih1 hentry (some PanSemResultExact.break, postContext) hbody)
  case case16 =>
      rename_i inst context state condition body value hcond hw hclock entry entryContext
        result postContext hbody fixed fixedContext hcont hnone hbreak ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change (decClockHOLExact state).FiniteSupport
        exact PanSemStateExact.finiteSupport_decClock h
      exact PanSemStateExact.finiteSupport_fixClock entry (result, postContext.state)
        (ih1 hentry (result, postContext) hbody)
  case case23 =>
      rename_i inst context state info function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (none, postContext.state)
        (ih1 hentry (none, postContext) hbody)
  case case24 =>
      rename_i inst context state info function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (some PanSemResultExact.break, postContext.state)
        (ih1 hentry (some PanSemResultExact.break, postContext) hbody)
  case case25 =>
      rename_i inst context state info function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (some PanSemResultExact.continue, postContext.state)
        (ih1 hentry (some PanSemResultExact.continue, postContext) hbody)
  case case26 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value hshape hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  case case27 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value hshape snd hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
      change ({ fixedContext.state with locals := state.locals } : PanSemStateExact width σ).FiniteSupport
      exact PanSemStateExact.finiteSupport_setLocals fixedContext.state state.locals h.1 hfixed
  case case28 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value hshape kind name snd hvalid hbody fixed
        fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
      change (setKvarHOLExact kind name value
        ({ fixedContext.state with locals := state.locals } : PanSemStateExact width σ)).FiniteSupport
      exact PanSemStateExact.finiteSupport_setKvar
        (PanSemStateExact.finiteSupport_setLocals fixedContext.state state.locals h.1 hfixed) kind name value
  case case29 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value hshape kind name snd hvalid hbody fixed
        fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
  case case30 =>
      rename_i inst context state info function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value hshape hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
  case case31 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext exceptionId value hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception exceptionId value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.exception exceptionId value), postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  case case32 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext exceptionId value fst hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception exceptionId value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.exception exceptionId value), postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  case case33 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape
        hcond heshapes hbody fixed fixedContext handlerState handlerContext ih2 ih1
      intro result hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception handlerId value), postContext.state)
        (ih2 hentry (some (PanSemResultExact.exception handlerId value), postContext) hbody)
      have hhandler : handlerContext.state.FiniteSupport := by
        change (setVarHOLExact handlerVar value
          ({ fixedContext.state with locals := state.locals } : PanSemStateExact width σ)).FiniteSupport
        exact PanSemStateExact.finiteSupport_setVar
          (PanSemStateExact.finiteSupport_setLocals fixedContext.state state.locals h.1 hfixed)
          handlerVar value
      exact ih1 hhandler result hres
  case case34 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape
        hcond heshapes hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception handlerId value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.exception handlerId value), postContext) hbody)
  case case35 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram
        heshapes hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception handlerId value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.exception handlerId value), postContext) hbody)
  case case36 =>
      rename_i inst context state function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext exceptionId value fst handlerId handlerVar
        handlerProgram hne hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.exception exceptionId value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.exception exceptionId value), postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  case case37 =>
      rename_i inst context state info function arguments values hargs body calleeLocals returnShape
        hlookup hclock entry entryContext postContext other hbreak hcont hret hexc hbody fixed
        fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry (some other, postContext.state)
        (ih1 hentry (some other, postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  case case42 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (none, postContext.state)
        (ih1 hentry (none, postContext) hbody)
  case case43 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (some PanSemResultExact.break, postContext.state)
        (ih1 hentry (some PanSemResultExact.break, postContext) hbody)
  case case44 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry (some PanSemResultExact.continue, postContext.state)
        (ih1 hentry (some PanSemResultExact.continue, postContext) hbody)
  case case46 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext1 value hcond result postContext
        restored hbody fixed fixedContext continuationState continuationContext hcont ih2 ih1
      intro r hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext1.state)
        (ih2 hentry (some (PanSemResultExact.returned value), postContext1) hbody)
      have hcontEntry : continuationContext.state.FiniteSupport := by
        change (setVarHOLExact resultName value
          ({ fixedContext.state with locals := state.locals } : PanSemStateExact width σ)).FiniteSupport
        exact PanSemStateExact.finiteSupport_setVar
          (PanSemStateExact.finiteSupport_setLocals fixedContext.state state.locals h.1 hfixed)
          resultName value
      have hcontF : postContext.state.FiniteSupport := ih1 hcontEntry (result, postContext) hcont
      change ({ postContext.state with locals := resVarHOLExact postContext.state.locals (resultName, state.locals resultName) } : PanSemStateExact width σ).FiniteSupport
      exact ⟨resVarHOLExact_finiteSupport postContext.state.locals
        (resultName, state.locals resultName) hcontF.1, hcontF.2.1, hcontF.2.2.1, hcontF.2.2.2⟩
  case case47 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext value hshape hbody fixed
        fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      exact PanSemStateExact.finiteSupport_fixClock entry
        (some (PanSemResultExact.returned value), postContext.state)
        (ih1 hentry (some (PanSemResultExact.returned value), postContext) hbody)
  case case48 =>
      rename_i inst context state resultName shape function arguments continuation values hargs body
        calleeLocals returnShape hlookup hclock entry entryContext postContext other hbreak hcont hret hbody
        fixed fixedContext ih1
      intro result hres
      simp only [Option.some.injEq] at hres
      cases hres
      have hentry : entryContext.state.FiniteSupport := by
        change ({ state with clock := state.clock - 1, locals := calleeLocals } : PanSemStateExact width σ).FiniteSupport
        exact callEntryHOLExact_finiteSupport state calleeLocals function values body returnShape hlookup h
      have hfixed := PanSemStateExact.finiteSupport_fixClock entry (some other, postContext.state)
        (ih1 hentry (some other, postContext) hbody)
      change (emptyLocalsHOLExact fixedContext.state).FiniteSupport
      exact PanSemStateExact.finiteSupport_emptyLocals hfixed
  all_goals closeCase

/-- Flapjack-specific invariant of the nonrecursive clause dispatcher: its
    post-state retains the source memory-address domain. HOL has no separate
    declaration for this dispatcher or this lemma; it supports the direct
    finite-carrier port of `evaluate_def`. -/
theorem evalPanSemNonrecursiveHOLExact_memaddrs {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (output : Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalPanSemNonrecursiveHOLExact program state = some output) :
    output.2.memaddrs = state.memaddrs := by
  cases program with
  | assign kind name value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalHOLExact state value with
      | none => simp [assignStepHOLExact, hEval]
      | some v =>
          by_cases hvalid : isValidValueHOLExact state kind name v = true
          · cases kind <;> simp [assignStepHOLExact, hEval, hvalid, setKvarHOLExact]
          · simp [assignStepHOLExact, hEval, hvalid]
  | primitive name operator args =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalListHOLExact state args with
      | none => simp [primitiveStepHOLExact, hEval]
      | some values =>
          cases hPrim : panPrimopHOLExact (width := width) operator values with
          | none => simp [primitiveStepHOLExact, hEval, hPrim]
          | some v =>
              by_cases hvalid : isValidValueHOLExact state .local name v = true
              · simp [primitiveStepHOLExact, hEval, hPrim, hvalid, setVarHOLExact]
              · simp [primitiveStepHOLExact, hEval, hPrim, hvalid]
  | store address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [storeStepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | store32 address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [store32StepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | storeByte address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [storeByteStepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | extCall function configuration configurationLength array arrayLength =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact extCallStepHOLExact_memaddrs state
        (fun _ expression => evalHOLExact state expression) function
        configuration configurationLength array arrayLength
  | raise exception value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalHOLExact state value with
      | none => simp [raiseStepHOLExact, hEval]
      | some v =>
          cases hshape : state.eshapes exception with
          | none => simp [raiseStepHOLExact, hEval, hshape]
          | some shp =>
              simp only [raiseStepHOLExact, hEval, hshape]
              split
              · split <;> rfl
              · rfl
  | «return» value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [returnStepHOLExact]; split
      · split <;> rfl
      · rfl
  | shMemLoad size kind name address =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact (shMemLoadClauseHOLExact_preservesDomains state size kind name address
        (fun _ expression => evalHOLExact state expression)).1
  | shMemStore size address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact (shMemStoreClauseHOLExact_preservesDomains state size address value
        (fun _ expression => evalHOLExact state expression)).1
  | tick =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [tickStepHOLExact]; split <;> rfl
  | skip =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | dec _ _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | seq _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | ite _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | «while» _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | «break» =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | «continue» =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | call _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | decCall _ _ _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | annot _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl

/-- Flapjack-specific shared-memory domain invariant of the nonrecursive
    clause dispatcher. There is no standalone HOL declaration to tag; this
    lemma is infrastructure for the finite-carrier `evaluate_def` port. -/
theorem evalPanSemNonrecursiveHOLExact_shMemaddrs {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (output : Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalPanSemNonrecursiveHOLExact program state = some output) :
    output.2.shMemaddrs = state.shMemaddrs := by
  cases program with
  | assign kind name value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalHOLExact state value with
      | none => simp [assignStepHOLExact, hEval]
      | some v =>
          by_cases hvalid : isValidValueHOLExact state kind name v = true
          · cases kind <;> simp [assignStepHOLExact, hEval, hvalid, setKvarHOLExact]
          · simp [assignStepHOLExact, hEval, hvalid]
  | primitive name operator args =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalListHOLExact state args with
      | none => simp [primitiveStepHOLExact, hEval]
      | some values =>
          cases hPrim : panPrimopHOLExact (width := width) operator values with
          | none => simp [primitiveStepHOLExact, hEval, hPrim]
          | some v =>
              by_cases hvalid : isValidValueHOLExact state .local name v = true
              · simp [primitiveStepHOLExact, hEval, hPrim, hvalid, setVarHOLExact]
              · simp [primitiveStepHOLExact, hEval, hPrim, hvalid]
  | store address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [storeStepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | store32 address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [store32StepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | storeByte address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [storeByteStepHOLExact]; split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | extCall function configuration configurationLength array arrayLength =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact extCallStepHOLExact_shMemaddrs state
        (fun _ expression => evalHOLExact state expression) function
        configuration configurationLength array arrayLength
  | raise exception value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      cases hEval : evalHOLExact state value with
      | none => simp [raiseStepHOLExact, hEval]
      | some v =>
          cases hshape : state.eshapes exception with
          | none => simp [raiseStepHOLExact, hEval, hshape]
          | some shp =>
              simp only [raiseStepHOLExact, hEval, hshape]
              split
              · split <;> rfl
              · rfl
  | «return» value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [returnStepHOLExact]; split
      · split <;> rfl
      · rfl
  | shMemLoad size kind name address =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact (shMemLoadClauseHOLExact_preservesDomains state size kind name address
        (fun _ expression => evalHOLExact state expression)).2
  | shMemStore size address value =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      exact (shMemStoreClauseHOLExact_preservesDomains state size address value
        (fun _ expression => evalHOLExact state expression)).2
  | tick =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h
      simp only [tickStepHOLExact]; split <;> rfl
  | skip =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | dec _ _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | seq _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | ite _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | «while» _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | «break» =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | «continue» =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl
  | call _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | decCall _ _ _ _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      exact absurd h (by simp)
  | annot _ _ =>
      simp only [evalPanSemNonrecursiveHOLExact] at h
      obtain rfl := Option.some.inj h; rfl

end Flapjack
