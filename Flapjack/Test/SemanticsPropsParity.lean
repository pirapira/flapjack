import Flapjack.SemanticsProps

/-!
Kernel regressions for the generic Cake behavior extension used by
`semantics_compile`. The carrier and set clauses are reviewed against
`semanticsPropsScript.sml:204-295`.
-/

namespace Flapjack.Test.SemanticsPropsParity

open Flapjack

def emptyLazyTrace : CakeLazyList FfiEvent :=
  { get? := fun _ => none
    none_suffix := by intro index hindex later _; exact hindex }

def succeedsWithoutEvents : CakeBehaviourSet := fun behaviour =>
  behaviour = .terminate .success []

def divergesWithoutEvents : CakeBehaviourSet := fun behaviour =>
  behaviour = .diverge emptyLazyTrace

theorem resourceLimit_prefix_of_termination :
    cakeExtendWithResourceLimit succeedsWithoutEvents
      (.terminate .resourceLimitHit []) := by
  apply Or.inr
  apply Or.inl
  exact ⟨[], .success, [], rfl, rfl, by simp [cakeListPrefix]⟩

theorem resourceLimit_prefix_of_divergence :
    cakeExtendWithResourceLimit divergesWithoutEvents
      (.terminate .resourceLimitHit []) := by
  apply Or.inr
  apply Or.inr
  exact ⟨[], emptyLazyTrace, rfl, rfl, by simp [cakeLprefix]⟩

theorem fail_is_not_added_to_resource_limit_extension :
    ¬ cakeExtendWithResourceLimit succeedsWithoutEvents .fail := by
  intro h
  have hne := cakeExtend_not_fail succeedsWithoutEvents .fail h (by simp [succeedsWithoutEvents])
  exact hne rfl

theorem implements_prime_trans_regression {source middle target : CakeBehaviourSet}
    {precise : Bool} (hmiddle : cakeImplements' precise middle target)
    (hsource : cakeImplements' precise source middle) :
    cakeImplements' precise source target :=
  cakeImplements'_trans hmiddle hsource

end Flapjack.Test.SemanticsPropsParity
