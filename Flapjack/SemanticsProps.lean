import Flapjack.Ffi

/-!
# CakeML generic behavior semantics

This is the generic behavior carrier and resource-limit extension from
`cakeml/semantics/ffi/ffiScript.sml` and
`cakeml/semantics/proofs/semanticsPropsScript.sml:204-225`.

The existing Pancake and Loop observational wrappers are program-specific
views; the backend `semantics_compile` theorem instead composes sets of these
generic Cake behaviors. `CakeLazyList` represents HOL `llist` values as
possibly finite sequences with no gaps.
-/

namespace Flapjack

/- Port status: these definitions follow the HOL constructor and relation
   clauses, but they are not tagged as exact ports. The Lean `CakeLazyList`
   representation below has no checked bridge to HOL's `llist`, and there is
   no verified source-to-Lean representation relation for this behavior
   carrier. `cakeImplements'_trans` is therefore a kernel-checked structural
   analogue until those carrier correspondences are established. -/
/-- A HOL lazy list (`llist`): a finite prefix may end, after which all reads
    are absent, or the list may continue indefinitely. -/
structure CakeLazyList (α : Type u) where
  get? : Nat → Option α
  none_suffix : ∀ index, get? index = none → ∀ later, index ≤ later → get? later = none

/-- `LPREFIX (fromList xs) trace` from HOL: every element of the finite list
    agrees with the same position in the lazy list. -/
def cakeLprefix (xs : List α) (trace : CakeLazyList α) : Prop :=
  ∀ index, index < xs.length → trace.get? index = xs[index]?

/-- The finite-list prefix relation used by Cake's `≼`. -/
def cakeListPrefix (xs ys : List α) : Prop :=
  xs.length ≤ ys.length ∧ ∀ index, index < xs.length → xs[index]? = ys[index]?

theorem cakeListPrefix_trans {xs ys zs : List α}
    (hxy : cakeListPrefix xs ys) (hyz : cakeListPrefix ys zs) :
    cakeListPrefix xs zs := by
  have hlenxy := hxy.1
  have hlenyz := hyz.1
  constructor
  · omega
  · intro index hindex
    rw [hxy.2 index hindex]
    exact hyz.2 index (by omega)

theorem cakeListPrefix_lprefix_trans {xs ys : List α}
    {trace : CakeLazyList α} (hxy : cakeListPrefix xs ys)
    (htrace : cakeLprefix ys trace) : cakeLprefix xs trace := by
  have hlenxy := hxy.1
  intro index hindex
  rw [hxy.2 index hindex]
  exact htrace index (by omega)

/-- `outcome` from Cake's generic semantics, where a terminal FFI event is
    distinct from successful completion and resource exhaustion. -/
inductive CakeOutcome where
  | success
  | resourceLimitHit
  | ffi (event : FfiFinalEvent)
  deriving DecidableEq, Repr

/-- The three constructors of Cake's generic `behaviour` datatype. -/
inductive CakeBehaviour where
  | diverge (trace : CakeLazyList FfiEvent)
  | terminate (outcome : CakeOutcome) (events : List FfiEvent)
  | fail

/-- HOL sets are represented by their membership predicates. -/
abbrev CakeBehaviourSet := CakeBehaviour → Prop

/-- Membership in HOL `extend_with_resource_limit`: retain existing
    behaviors, allow finite prefixes of terminating traces, and allow finite
    prefixes of divergent traces as resource-limit termination. -/
def cakeExtendWithResourceLimit (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour) : Prop :=
  behaviours result ∨
    (∃ events outcome complete,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.terminate outcome complete) ∧
        cakeListPrefix events complete) ∨
    (∃ events trace,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.diverge trace) ∧ cakeLprefix events trace)

/-- The precise flag chooses either the original behavior set or its
    resource-limit extension, matching `extend_with_resource_limit'`. -/
def cakeExtendWithResourceLimit' (precise : Bool)
    (behaviours : CakeBehaviourSet) : CakeBehaviourSet :=
  if precise then behaviours else cakeExtendWithResourceLimit behaviours

/-- Cake's `implements' precise x y`: compiled behavior `x` refines source
    behavior `y`, modulo the resource-limit extension. This remains an
    untagged carrier analogue until the HOL/Lean behavior relation is checked. -/
def cakeImplements' (precise : Bool) (compiled source : CakeBehaviourSet) : Prop :=
  ¬ source .fail → ∀ result, compiled result →
    cakeExtendWithResourceLimit' precise source result

theorem cakeExtend_not_fail (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour) (hresult : cakeExtendWithResourceLimit behaviours result)
    (hfail : ¬ behaviours .fail) : result ≠ .fail := by
  rcases hresult with hresult | hresult | hresult
  · intro heq
    subst result
    exact hfail hresult
  · rcases hresult with ⟨events, outcome, complete, heq, _, _⟩
    cases heq <;> simp
  · rcases hresult with ⟨events, trace, heq, _, _⟩
    cases heq <;> simp

/-- Extending behaviors twice adds no new resource-limit observations: list
    prefix and lazy-list prefix are transitive. This is the set-inclusion core
    needed by Cake's `implements'_trans`. -/
theorem cakeExtendWithResourceLimit_idempotent (behaviours : CakeBehaviourSet)
    (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit
      (cakeExtendWithResourceLimit behaviours) result) :
    cakeExtendWithResourceLimit behaviours result := by
  rcases hresult with hresult | hresult | hresult
  · exact hresult
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    change cakeExtendWithResourceLimit behaviours (.terminate outcome complete) at hcomplete
    rcases hcomplete with hcomplete | hcomplete | hcomplete
    · exact Or.inr (Or.inl ⟨events, outcome, complete, rfl, hcomplete, hpref⟩)
    · rcases hcomplete with ⟨middle, middleOutcome, middleComplete, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inl ⟨events, middleOutcome, middleComplete, rfl, hmiddle,
        cakeListPrefix_trans hpref hmidPrefix⟩)
    · rcases hcomplete with ⟨middle, trace, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inr ⟨events, trace, rfl, hmiddle,
        cakeListPrefix_lprefix_trans hpref hmidPrefix⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    change cakeExtendWithResourceLimit behaviours (.diverge trace) at htrace
    rcases htrace with htrace | htrace | htrace
    · exact Or.inr (Or.inr ⟨events, trace, rfl, htrace, hpref⟩)
    · rcases htrace with ⟨_, _, _, hdiverge, _⟩
      cases hdiverge
    · rcases htrace with ⟨_, _, hdiverge, _⟩
      cases hdiverge

theorem cakeExtendWithResourceLimit'_idempotent (precise : Bool)
    (behaviours : CakeBehaviourSet) (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit' precise
      (cakeExtendWithResourceLimit' precise behaviours) result) :
    cakeExtendWithResourceLimit' precise behaviours result := by
  cases precise with
  | true => exact hresult
  | false => exact cakeExtendWithResourceLimit_idempotent behaviours result hresult

theorem cakeExtendWithResourceLimit_mono {left right : CakeBehaviourSet}
    (hsubset : ∀ result, left result → right result) (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit left result) :
    cakeExtendWithResourceLimit right result := by
  rcases hresult with hresult | hresult | hresult
  · exact Or.inl (hsubset result hresult)
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    exact Or.inr (Or.inl ⟨events, outcome, complete, rfl,
      hsubset (.terminate outcome complete) hcomplete, hpref⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    exact Or.inr (Or.inr ⟨events, trace, rfl, hsubset (.diverge trace) htrace, hpref⟩)

theorem cakeExtendWithResourceLimit'_mono (precise : Bool)
    {left right : CakeBehaviourSet} (hsubset : ∀ result, left result → right result)
    (result : CakeBehaviour)
    (hresult : cakeExtendWithResourceLimit' precise left result) :
    cakeExtendWithResourceLimit' precise right result := by
  cases precise with
  | false => exact cakeExtendWithResourceLimit_mono hsubset result hresult
  | true => exact hsubset result hresult

/-- Structural analogue of HOL `implements'_trans` from
    `semanticsPropsScript.sml:285-295`, with the representation gap noted at
    `CakeLazyList`. -/
theorem cakeImplements'_trans {compiled intermediate source : CakeBehaviourSet}
    {precise : Bool} (hintermediate : cakeImplements' precise intermediate source)
    (hcompiled : cakeImplements' precise compiled intermediate) :
    cakeImplements' precise compiled source := by
  intro hsourceFail result hresult
  have hintermediateSubset := hintermediate hsourceFail
  have hintermediateFail : ¬ intermediate .fail := by
    intro hfail
    have hfailExtended : cakeExtendWithResourceLimit' precise source .fail :=
      hintermediateSubset .fail hfail
    cases precise with
    | false => exact cakeExtend_not_fail source .fail hfailExtended hsourceFail rfl
    | true => exact hsourceFail hfailExtended
  have hcompiledSubset := hcompiled hintermediateFail
  have hcompiledExtended := cakeExtendWithResourceLimit'_mono precise hintermediateSubset result
    (hcompiledSubset result hresult)
  exact cakeExtendWithResourceLimit'_idempotent precise source
    result hcompiledExtended

end Flapjack
