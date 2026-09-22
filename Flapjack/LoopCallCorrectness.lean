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

theorem lookup_of_delete
    (environment : LocationEnv) (name destination location : Nat)
    (hlookup : lookup name (delete destination environment) = some location) :
    lookup name environment = some location := by
  by_cases hname : name = destination
  · subst name
    rw [lookup_delete_same] at hlookup
    simp at hlookup
  · have hsame := lookup_delete_other destination name environment hname
    rw [← hsame]
    exact hlookup

theorem labelsIn_delete_update
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination : Nat) (hvalue : α)
    (henvironment : labelsIn environment locals) :
    labelsIn (delete destination environment)
      (updateLoopLocal locals destination hvalue) := by
  intro name location hlookup
  have hlookup' := lookup_of_delete environment name destination location hlookup
  obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup'
  by_cases hlocation : location = destination
  · subst location
    exact ⟨hvalue, by simp [updateLoopLocal]⟩
  · exact ⟨oldValue, by simpa [updateLoopLocal, hlocation] using holdValue⟩

theorem labelsIn_load32_update
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination : Nat) (value : α)
    (henvironment : labelsIn environment locals) :
    labelsIn
      (match lookup destination environment with
      | none => environment
      | some _ => delete destination environment)
      (updateLoopLocal locals destination value) := by
  cases hdestination : lookup destination environment with
  | none =>
      change labelsIn environment
        (updateLoopLocal locals destination value)
      intro name location hlookup
      obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup
      by_cases hlocation : location = destination
      · subst location
        exact ⟨value, by simp [updateLoopLocal]⟩
      · exact ⟨oldValue, by simpa [updateLoopLocal, hlocation] using holdValue⟩
  | some oldValue =>
      change labelsIn (delete destination environment)
        (updateLoopLocal locals destination value)
      exact labelsIn_delete_update environment locals destination value
        henvironment

theorem comp_load32_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address destination : Nat) (addressValue value : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.memory addressValue = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.load32 address destination : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn (comp environment (.load32 address destination : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hcompiled :
      comp environment (.load32 address destination : LoopProg α) =
        (.load32 address destination,
          match lookup destination environment with
          | none => environment
          | some _ => delete destination environment) := by
    simp [comp] <;> rfl
  rw [hcompiled]
  constructor
  · exact evalLoopProg_load32 state address destination addressValue value
      haddress hvalue
  · exact labelsIn_load32_update environment state.locals destination value
      henvironment

theorem comp_loadByte_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address destination : Nat) (addressValue value : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.memory addressValue = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.loadByte address destination : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn (comp environment (.loadByte address destination : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hcompiled :
      comp environment (.loadByte address destination : LoopProg α) =
        (.loadByte address destination,
          match lookup destination environment with
          | none => environment
          | some _ => delete destination environment) := by
    simp [comp] <;> rfl
  rw [hcompiled]
  constructor
  · exact evalLoopProg_loadByte state address destination addressValue value
      haddress hvalue
  · exact labelsIn_load32_update environment state.locals destination value
      henvironment

theorem comp_store32_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address value : Nat) (addressValue valueValue : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.locals value = some valueValue)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.store32 address value : LoopProg α)).1 =
        some (.normal { state with
          memory := updateLoopMemory state.memory addressValue valueValue }) ∧
      labelsIn (comp environment (.store32 address value : LoopProg α)).2
        ({ state with
          memory := updateLoopMemory state.memory addressValue valueValue }).locals := by
  have hcompiled :
      comp environment (.store32 address value : LoopProg α) =
        (.store32 address value, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_store32 state address value addressValue valueValue
      haddress hvalue
  · exact henvironment

theorem comp_storeByte_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address value : Nat) (addressValue valueValue : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.locals value = some valueValue)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.storeByte address value : LoopProg α)).1 =
        some (.normal { state with
          memory := updateLoopMemory state.memory addressValue valueValue }) ∧
      labelsIn (comp environment (.storeByte address value : LoopProg α)).2
        ({ state with
          memory := updateLoopMemory state.memory addressValue valueValue }).locals := by
  have hcompiled :
      comp environment (.storeByte address value : LoopProg α) =
        (.storeByte address value, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_storeByte state address value addressValue valueValue
      haddress hvalue
  · exact henvironment

theorem comp_store_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address : LoopExp α) (value : Nat)
    (addressValue valueValue : α)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.locals value = some valueValue)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.store address value : LoopProg α)).1 =
        some (.normal { state with
          memory := updateLoopMemory state.memory addressValue valueValue }) ∧
      labelsIn (comp environment (.store address value : LoopProg α)).2
        ({ state with
          memory := updateLoopMemory state.memory addressValue valueValue }).locals := by
  have hcompiled :
      comp environment (.store address value : LoopProg α) =
        (.store address value, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_store state address value addressValue valueValue
      haddress hvalue
  · exact henvironment

end LoopCall
end Flapjack
