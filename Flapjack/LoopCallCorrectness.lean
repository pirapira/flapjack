import Flapjack.LoopCall
import Flapjack.LoopSemantics

namespace Flapjack
namespace LoopCall

/-! Value-level counterpart of Cake's `labels_in` invariant for `loop_call`. -/
def labelsIn (environment : LocationEnv) (locals : Nat → Option α) : Prop :=
  ∀ name source, lookup name environment = some source →
    ∃ value, locals source = some value

theorem labelsIn_insert_update
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination source : Nat) (value : α)
    (hsource : locals source = some value)
    (henvironment : labelsIn environment locals) :
    labelsIn (insert destination source environment)
      (updateLoopLocal locals destination value) := by
  intro name location hlookup
  by_cases hdestination : destination = name
  · subst name
    have hsourceLocation : source = location := by
      simpa [insert, lookup] using hlookup
    have hlocation : location = source := hsourceLocation.symm
    subst location
    exact ⟨value, by
      by_cases hsourceDestination : source = destination
      · subst source
        simp [updateLoopLocal]
      · simpa [updateLoopLocal, hsourceDestination] using hsource⟩
  · have hlookup' : lookup name environment = some location := by
      simpa [insert, lookup, hdestination] using hlookup
    obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup'
    by_cases hsame : location = destination
    · subst location
      exact ⟨value, by simp [updateLoopLocal]⟩
    · exact ⟨oldValue, by simp [updateLoopLocal, hsame, holdValue]⟩

theorem comp_locValue_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (destination source : Nat) (value : α)
    (hvalue : state.locals source = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.locValue destination source : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn (comp environment (.locValue destination source : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hcompiled :
      comp environment (.locValue destination source : LoopProg α) =
        (.locValue destination source, insert destination source environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_locValue state destination source value hvalue
  · exact labelsIn_insert_update environment state.locals destination source
      value hvalue henvironment

end LoopCall
end Flapjack
