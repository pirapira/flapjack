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

theorem labelsIn_update
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination : Nat) (value : α)
    (henvironment : labelsIn environment locals) :
    labelsIn environment (updateLoopLocal locals destination value) := by
  intro name location hlookup
  obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup
  by_cases hsame : location = destination
  · subst location
    exact ⟨value, by simp [updateLoopLocal]⟩
  · exact ⟨oldValue, by simpa [updateLoopLocal, hsame] using holdValue⟩

theorem labelsIn_insert_update_any
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination source : Nat) (sourceValue value : α)
    (hsource : locals source = some sourceValue)
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
    by_cases hsourceDestination : source = destination
    · subst source
      exact ⟨value, by simp [updateLoopLocal]⟩
    · exact ⟨sourceValue, by
        simpa [updateLoopLocal, hsourceDestination] using hsource⟩
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

theorem comp_skip_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.skip : LoopProg α)).1 =
        some (.normal state) ∧
      labelsIn (comp environment (.skip : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.skip : LoopProg α) = (.skip, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_skip state
  · exact henvironment

theorem comp_assign_var_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (destination source : Nat) (value : α)
    (hvalue : state.locals source = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.assign destination (.var source) : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn
        (comp environment (.assign destination (.var source) : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hexpression : evalLoopExp state (.var source) = some value :=
    evalLoopExp_var state source value hvalue
  cases hdestination : lookup destination environment with
  | none =>
      cases hsource : lookup source environment with
      | none =>
          have hcompiled :
              comp environment (.assign destination (.var source) : LoopProg α) =
                (.assign destination (.var source), environment) := by
            simp [comp, hdestination, hsource]
          rw [hcompiled]
          constructor
          · exact evalLoopProg_assign state destination (.var source) value hexpression
          · exact labelsIn_update environment state.locals destination value henvironment
      | some location =>
          have hcompiled :
              comp environment (.assign destination (.var source) : LoopProg α) =
                (.assign destination (.var source), insert destination location environment) := by
            simp [comp, hdestination, hsource]
          obtain ⟨sourceValue, hsourceValue⟩ := henvironment source location hsource
          rw [hcompiled]
          constructor
          · exact evalLoopProg_assign state destination (.var source) value hexpression
          · exact labelsIn_insert_update_any environment state.locals destination location
              sourceValue value hsourceValue henvironment
  | some _ =>
      cases hsource : lookup source environment with
      | none =>
          have hcompiled :
              comp environment (.assign destination (.var source) : LoopProg α) =
                (.assign destination (.var source), delete destination environment) := by
            simp [comp, hdestination, hsource]
          rw [hcompiled]
          constructor
          · exact evalLoopProg_assign state destination (.var source) value hexpression
          · exact labelsIn_delete_update environment state.locals destination value henvironment
      | some location =>
          have hcompiled :
              comp environment (.assign destination (.var source) : LoopProg α) =
                (.assign destination (.var source), insert destination location environment) := by
            simp [comp, hdestination, hsource]
          obtain ⟨sourceValue, hsourceValue⟩ := henvironment source location hsource
          rw [hcompiled]
          constructor
          · exact evalLoopProg_assign state destination (.var source) value hexpression
          · exact labelsIn_insert_update_any environment state.locals destination location
              sourceValue value hsourceValue henvironment

theorem comp_assign_nonvar_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (destination : Nat) (expression : LoopExp α) (value : α)
    (hnotvar : ∀ source, expression ≠ .var source)
    (hvalue : evalLoopExp state expression = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.assign destination expression : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn
        (comp environment (.assign destination expression : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hcompiled :
      comp environment (.assign destination expression : LoopProg α) =
        (.assign destination expression,
          match lookup destination environment with
          | none => environment
          | some _ => delete destination environment) := by
    cases expression <;> simp_all [comp] <;> rfl
  rw [hcompiled]
  cases hdestination : lookup destination environment with
  | none =>
      constructor
      · exact evalLoopProg_assign state destination expression value hvalue
      · exact labelsIn_update environment state.locals destination value henvironment
  | some _ =>
      constructor
      · exact evalLoopProg_assign state destination expression value hvalue
      · exact labelsIn_delete_update environment state.locals destination value henvironment

theorem comp_tick_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (_henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.tick : LoopProg α)).1 =
        some (.normal state) ∧
      labelsIn (comp environment (.tick : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.tick : LoopProg α) = (.tick, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_tick state
  · simp [labelsIn, lookup]

theorem comp_setGlobal_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (address : α) (expression : LoopExp α) (value : α)
    (hvalue : evalLoopExp state expression = some value)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.setGlobal address expression : LoopProg α)).1 =
        some (.normal { state with
          globals := updateLoopGlobal state.globals address value }) ∧
      labelsIn (comp environment (.setGlobal address expression : LoopProg α)).2
        ({ state with globals := updateLoopGlobal state.globals address value }).locals := by
  have hcompiled :
      comp environment (.setGlobal address expression : LoopProg α) =
        (.setGlobal address expression, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · simp [evalLoopProg, hvalue]
  · exact henvironment

theorem lookup_of_listDelete
    (destinations : List Nat) (environment : LocationEnv)
    (name location : Nat)
    (hlookup : lookup name (listDelete destinations environment) = some location) :
    lookup name environment = some location := by
  induction destinations generalizing environment with
  | nil => simpa [listDelete] using hlookup
  | cons destination destinations ih =>
      change lookup name (listDelete destinations (delete destination environment)) =
        some location at hlookup
      have hafter := ih (environment := delete destination environment) hlookup
      exact lookup_of_delete environment name destination location hafter

theorem labelsIn_listDelete
    (destinations : List Nat) (environment : LocationEnv)
    (locals : Nat → Option α)
    (henvironment : labelsIn environment locals) :
    labelsIn (listDelete destinations environment) locals := by
  intro name location hlookup
  exact henvironment name location
    (lookup_of_listDelete destinations environment name location hlookup)

theorem comp_primitive_labelsIn
    (environment : LocationEnv) (destinations : List Nat)
    (operator : PrimOp) (arguments : List Nat)
    (locals : Nat → Option α)
    (henvironment : labelsIn environment locals) :
    (comp environment (.primitive destinations operator arguments : LoopProg α)).1 =
        .primitive destinations operator arguments ∧
      labelsIn
        (comp environment (.primitive destinations operator arguments : LoopProg α)).2
        locals := by
  have hcompiled :
      comp environment (.primitive destinations operator arguments : LoopProg α) =
        (.primitive destinations operator arguments, listDelete destinations environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · rfl
  · exact labelsIn_listDelete destinations environment locals henvironment

end LoopCall
end Flapjack
