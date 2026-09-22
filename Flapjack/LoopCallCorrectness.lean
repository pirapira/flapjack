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

theorem labelsIn_delete
    (environment : LocationEnv) (locals : Nat → Option α)
    (destination : Nat)
    (henvironment : labelsIn environment locals) :
    labelsIn (delete destination environment) locals := by
  intro name location hlookup
  exact henvironment name location
    (lookup_of_delete environment name destination location hlookup)

theorem labelsIn_delete_update_any
    (environment : LocationEnv) (locals : Nat → Option α)
    (deleteDestination updateDestination : Nat) (value : α)
    (henvironment : labelsIn environment locals) :
    labelsIn (delete deleteDestination environment)
      (updateLoopLocal locals updateDestination value) := by
  intro name location hlookup
  have hlookup' := lookup_of_delete environment name deleteDestination location hlookup
  obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup'
  by_cases hsame : location = updateDestination
  · subst location
    exact ⟨value, by simp [updateLoopLocal]⟩
  · exact ⟨oldValue, by simpa [updateLoopLocal, hsame] using holdValue⟩

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

theorem comp_fail_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.fail : LoopProg α)).1 = none ∧
      labelsIn (comp environment (.fail : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.fail : LoopProg α) = (.fail, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · simp [evalLoopProg]
  · exact henvironment

theorem comp_mark_labelsIn
    (environment : LocationEnv) (body : LoopProg α)
    (locals : Nat → Option α)
    (hbody : labelsIn (comp environment body).2 locals) :
    (comp environment (.mark body : LoopProg α)).1 =
        .mark (comp environment body).1 ∧
      labelsIn (comp environment (.mark body : LoopProg α)).2 locals := by
  have hcompiled :
      comp environment (.mark body : LoopProg α) =
        (.mark (comp environment body).1, (comp environment body).2) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · rfl
  · exact hbody

theorem comp_mark_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (body : LoopProg α) (result : LoopResult α)
    (hbody : evalLoopProg fuel state (comp environment body).1 = some result)
    (hlabels : labelsIn (comp environment body).2
      (loopResultState result).locals) :
    evalLoopProg (fuel + 1) state
        (comp environment (.mark body : LoopProg α)).1 = some result ∧
      labelsIn (comp environment (.mark body : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment (.mark body : LoopProg α) =
        (.mark (comp environment body).1, (comp environment body).2) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · simp [evalLoopProg, hbody]
  · exact hlabels

theorem comp_seq_labelsIn
    (environment : LocationEnv) (first second : LoopProg α)
    (locals : Nat → Option α) :
    (comp environment (.seq first second : LoopProg α)).1 =
        .seq (comp environment first).1
          (comp (comp environment first).2 second).1 ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2 locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · rfl
  · simp [labelsIn, lookup]

theorem comp_seq_normal_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (first second : LoopProg α) (middle : LoopState α) (result : LoopResult α)
    (hfirst : evalLoopProg fuel state (comp environment first).1 = some (.normal middle))
    (hsecond :
      evalLoopProg fuel middle (comp (comp environment first).2 second).1 = some result) :
    evalLoopProg (fuel + 1) state
        (comp environment (.seq first second : LoopProg α)).1 = some result ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_seq_normal fuel state (comp environment first).1
      (comp (comp environment first).2 second).1 middle result hfirst hsecond
  · simp [labelsIn, lookup]

theorem comp_seq_returned_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (first second : LoopProg α) (middle : LoopState α) (values : List α)
    (hfirst :
      evalLoopProg fuel state (comp environment first).1 =
        some (.returned middle values)) :
    evalLoopProg (fuel + 1) state
        (comp environment (.seq first second : LoopProg α)).1 =
        some (.returned middle values) ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2
        middle.locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_seq_returned fuel state (comp environment first).1
      (comp (comp environment first).2 second).1 middle values hfirst
  · simp [labelsIn, lookup]

theorem comp_seq_broke_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (first second : LoopProg α) (middle : LoopState α) (label : Nat)
    (hfirst :
      evalLoopProg fuel state (comp environment first).1 =
        some (.broke middle label)) :
    evalLoopProg (fuel + 1) state
        (comp environment (.seq first second : LoopProg α)).1 =
        some (.broke middle label) ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2
        middle.locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_seq_broke fuel state (comp environment first).1
      (comp (comp environment first).2 second).1 middle label hfirst
  · simp [labelsIn, lookup]

theorem comp_seq_continued_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (first second : LoopProg α) (middle : LoopState α) (label : Nat)
    (hfirst :
      evalLoopProg fuel state (comp environment first).1 =
        some (.continued middle label)) :
    evalLoopProg (fuel + 1) state
        (comp environment (.seq first second : LoopProg α)).1 =
        some (.continued middle label) ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2
        middle.locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_seq_continued fuel state (comp environment first).1
      (comp (comp environment first).2 second).1 middle label hfirst
  · simp [labelsIn, lookup]

theorem comp_seq_raised_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (first second : LoopProg α) (middle : LoopState α) (exception : α)
    (hfirst :
      evalLoopProg fuel state (comp environment first).1 =
        some (.raised middle exception)) :
    evalLoopProg (fuel + 1) state
        (comp environment (.seq first second : LoopProg α)).1 =
        some (.raised middle exception) ∧
      labelsIn (comp environment (.seq first second : LoopProg α)).2
        middle.locals := by
  have hcompiled :
      comp environment (.seq first second : LoopProg α) =
        (.seq (comp environment first).1
          (comp (comp environment first).2 second).1, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_seq_raised fuel state (comp environment first).1
      (comp (comp environment first).2 second).1 middle exception hfirst
  · simp [labelsIn, lookup]

theorem comp_ite_labelsIn
    (environment : LocationEnv) (operator : Cmp) (condition : Nat)
    (right : RegImm α) (thenBranch elseBranch : LoopProg α)
    (live : List Nat) (locals : Nat → Option α) :
    (comp environment
      (.ite operator condition right thenBranch elseBranch live : LoopProg α)).1 =
        .ite operator condition right (comp environment thenBranch).1
          (comp environment elseBranch).1 live ∧
      labelsIn
        (comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α)).2
        locals := by
  have hcompiled :
      comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α) =
        (.ite operator condition right (comp environment thenBranch).1
          (comp environment elseBranch).1 live, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · rfl
  · simp [labelsIn, lookup]

theorem comp_ite_true_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (operator : Cmp) (condition : Nat) (right : RegImm α)
    (thenBranch elseBranch : LoopProg α) (live : List Nat)
    (leftValue rightValue : α) (result : LoopResult α)
    (hleft : state.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => state.locals name) = some rightValue)
    (hchoose : evalLoopCondition operator leftValue rightValue = some true)
    (hthen : evalLoopProg fuel state (comp environment thenBranch).1 = some result) :
    evalLoopProg (fuel + 1) state
        (comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α) =
        (.ite operator condition right (comp environment thenBranch).1
          (comp environment elseBranch).1 live, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_ite_true fuel state operator condition right
      (comp environment thenBranch).1 (comp environment elseBranch).1 live
      leftValue rightValue result hleft hright hchoose hthen
  · simp [labelsIn, lookup]

theorem comp_ite_false_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (operator : Cmp) (condition : Nat) (right : RegImm α)
    (thenBranch elseBranch : LoopProg α) (live : List Nat)
    (leftValue rightValue : α) (result : LoopResult α)
    (hleft : state.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => state.locals name) = some rightValue)
    (hchoose : evalLoopCondition operator leftValue rightValue = some false)
    ( helse : evalLoopProg fuel state (comp environment elseBranch).1 = some result) :
    evalLoopProg (fuel + 1) state
        (comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment
          (.ite operator condition right thenBranch elseBranch live : LoopProg α) =
        (.ite operator condition right (comp environment thenBranch).1
          (comp environment elseBranch).1 live, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_ite_false fuel state operator condition right
      (comp environment thenBranch).1 (comp environment elseBranch).1 live
      leftValue rightValue result hleft hright hchoose helse
  · simp [labelsIn, lookup]

theorem comp_loop_labelsIn
    (environment : LocationEnv) (liveIn liveOut : List Nat)
    (body : LoopProg α) (locals : Nat → Option α) :
    (comp environment (.loop liveIn body liveOut : LoopProg α)).1 =
        .loop liveIn (comp ([] : LocationEnv) body).1 liveOut ∧
      labelsIn
        (comp environment (.loop liveIn body liveOut : LoopProg α)).2
        locals := by
  have hcompiled :
      comp environment (.loop liveIn body liveOut : LoopProg α) =
        (.loop liveIn (comp ([] : LocationEnv) body).1 liveOut, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · rfl
  · simp [labelsIn, lookup]

/-! This is the evaluator-result part of Cake's `compile_correct[Loop]`.
    The source proof supplies the repeated-body result from its induction
    hypothesis; this theorem preserves that result through the compiled Loop
    wrapper and keeps the result-state `labelsIn` conclusion explicit. -/
theorem comp_loop_repeat_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (liveIn liveOut : List Nat) (body : LoopProg α)
    (result : LoopResult α)
    (hbody : evalLoopRepeat fuel state (comp ([] : LocationEnv) body).1 =
      some result) :
    evalLoopProg (fuel + 1) state
        (comp environment (.loop liveIn body liveOut : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment (.loop liveIn body liveOut : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment (.loop liveIn body liveOut : LoopProg α) =
        (.loop liveIn (comp ([] : LocationEnv) body).1 liveOut, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · simpa [evalLoopProg] using hbody
  · simp [labelsIn, lookup]

theorem comp_loop_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (liveIn liveOut : List Nat) (body : LoopProg α) (result : LoopResult α)
    (hresult : evalLoopRepeat fuel state
      (comp ([] : LocationEnv) body).1 = some result) :
    evalLoopProg (fuel + 1) state
        (comp environment (.loop liveIn body liveOut : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment (.loop liveIn body liveOut : LoopProg α)).2
        (loopResultState result).locals := by
  exact comp_loop_repeat_correct environment state fuel liveIn liveOut body result hresult

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

theorem comp_return_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (names : List Nat) (values : List α)
    (hvalues : loopReadLocals state.locals names = some values)
    (_henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.return names : LoopProg α)).1 =
        some (.returned state values) ∧
      labelsIn (comp environment (.return names : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.return names : LoopProg α) = (.return names, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_return state names values hvalues
  · simp [labelsIn, lookup]

theorem comp_raise_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (exception : Nat) (value : α)
    (hvalue : state.locals exception = some value)
    (_henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.raise exception : LoopProg α)).1 =
        some (.raised state value) ∧
      labelsIn (comp environment (.raise exception : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.raise exception : LoopProg α) = (.raise exception, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · simp [evalLoopProg, hvalue]
  · simp [labelsIn, lookup]

theorem comp_break_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (label : Nat)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.break label : LoopProg α)).1 =
        some (.broke state label) ∧
      labelsIn (comp environment (.break label : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.break label : LoopProg α) = (.break label, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_break state label
  · exact henvironment

theorem comp_continue_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α) (label : Nat)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.continue label : LoopProg α)).1 =
        some (.continued state label) ∧
      labelsIn (comp environment (.continue label : LoopProg α)).2 state.locals := by
  have hcompiled :
      comp environment (.continue label : LoopProg α) = (.continue label, environment) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_continue state label
  · exact henvironment

theorem comp_shMem_load_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
    (addressValue value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.memory addressValue = some value)
    (_henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.shMem operator name address : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals name value }) ∧
      labelsIn (comp environment (.shMem operator name address : LoopProg α)).2
        (updateLoopLocal state.locals name value) := by
  have hcompiled :
      comp environment (.shMem operator name address : LoopProg α) =
        (.shMem operator name address, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_shMem_load state operator name address addressValue value
      hoperator haddress hvalue
  · simp [labelsIn, lookup]

theorem comp_shMem_store_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
    (addressValue value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.locals name = some value)
    (_henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.shMem operator name address : LoopProg α)).1 =
        some (.normal { state with
          memory := updateLoopMemory state.memory addressValue value }) ∧
      labelsIn (comp environment (.shMem operator name address : LoopProg α)).2
        ({ state with memory := updateLoopMemory state.memory addressValue value }).locals := by
  have hcompiled :
      comp environment (.shMem operator name address : LoopProg α) =
        (.shMem operator name address, []) := by
    simp [comp]
  rw [hcompiled]
  constructor
  · exact evalLoopProg_shMem_store state operator name address addressValue value
      hoperator haddress hvalue
  · simp [labelsIn, lookup]

theorem comp_arith_div_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (destination dividend divisor : Nat)
    (dividendValue divisorValue : α)
    (hdividend : state.locals dividend = some dividendValue)
    (hdivisor : state.locals divisor = some divisorValue)
    (hnonzero : (divisorValue == 0) = false)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment (.arith (.div destination dividend divisor) : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination (dividendValue / divisorValue) }) ∧
      labelsIn
        (comp environment (.arith (.div destination dividend divisor) : LoopProg α)).2
        (updateLoopLocal state.locals destination (dividendValue / divisorValue)) := by
  have hcompiled :
      comp environment (.arith (.div destination dividend divisor) : LoopProg α) =
        (.arith (.div destination dividend divisor),
          match lookup destination environment with
          | none => environment
          | some _ => delete destination environment) := by
    simp [comp, compArith] <;> rfl
  rw [hcompiled]
  cases hdestination : lookup destination environment with
  | none =>
      constructor
      · exact evalLoopProg_div state destination dividend divisor dividendValue divisorValue
          hdividend hdivisor hnonzero
      · exact labelsIn_update environment state.locals destination
          (dividendValue / divisorValue) henvironment
  | some _ =>
      constructor
      · exact evalLoopProg_div state destination dividend divisor dividendValue divisorValue
          hdividend hdivisor hnonzero
      · exact labelsIn_delete_update environment state.locals destination
          (dividendValue / divisorValue) henvironment

theorem comp_arith_longMul_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (environment : LocationEnv) (state : LoopState α)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (leftValue rightValue : α)
    (hdestination : destinationLeft = destinationRight)
    (hleft : state.locals sourceLeft = some leftValue)
    (hright : state.locals sourceRight = some rightValue)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProg 1 state
        (comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destinationLeft (leftValue * rightValue) }) ∧
      labelsIn
        (comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : LoopProg α)).2
        (updateLoopLocal state.locals destinationLeft (leftValue * rightValue)) := by
  have hcompiled :
      comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : LoopProg α) =
        (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight),
          match lookup destinationLeft environment, lookup destinationRight environment with
          | none, none => environment
          | some _, none => delete destinationLeft environment
          | none, some _ => delete destinationRight environment
          | some _, some _ => delete destinationLeft (delete destinationRight environment)) := by
    simp [comp, compArith] <;> rfl
  have heval :
      evalLoopProg 1 state
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) =
        some (.normal { state with
          locals := updateLoopLocal state.locals destinationLeft (leftValue * rightValue) }) := by
    simp [evalLoopProg, hdestination, hleft, hright]
  rw [hcompiled]
  cases hleftDestination : lookup destinationLeft environment with
  | none =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_update environment state.locals destinationLeft
              (leftValue * rightValue) henvironment
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_delete_update_any environment state.locals destinationRight
              destinationLeft (leftValue * rightValue) henvironment
  | some _ =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_delete_update_any environment state.locals destinationLeft
              destinationLeft (leftValue * rightValue) henvironment
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_delete_update (delete destinationRight environment)
              state.locals destinationLeft (leftValue * rightValue)
              (labelsIn_delete environment state.locals destinationRight henvironment)

theorem comp_arith_longMul_full_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanCmp α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [Complement α]
    (longMul : α → α → Option (α × α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (leftValue rightValue highValue lowValue : α)
    (hleft : state.locals sourceLeft = some leftValue)
    (hright : state.locals sourceRight = some rightValue)
    (hcompute : longMul leftValue rightValue = some (highValue, lowValue))
    (henvironment : labelsIn environment state.locals) :
    evalLoopProgFullWithLongMul longMul (fuel + 1) state
        (comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) :
            LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal
            (updateLoopLocal state.locals destinationLeft highValue)
            destinationRight lowValue }) ∧
      labelsIn
        (comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) :
            LoopProg α)).2
        (updateLoopLocal
          (updateLoopLocal state.locals destinationLeft highValue)
          destinationRight lowValue) := by
  have hcompiled :
      comp environment
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) :
            LoopProg α) =
        (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight),
          match lookup destinationLeft environment, lookup destinationRight environment with
          | none, none => environment
          | some _, none => delete destinationLeft environment
          | none, some _ => delete destinationRight environment
          | some _, some _ => delete destinationLeft (delete destinationRight environment)) := by
    simp [comp, compArith] <;> rfl
  have heval :
      evalLoopProgFullWithLongMul longMul (fuel + 1) state
          (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) =
        some (.normal { state with
          locals := updateLoopLocal
            (updateLoopLocal state.locals destinationLeft highValue)
            destinationRight lowValue }) := by
    simp [evalLoopProgFullWithLongMul, hleft, hright, hcompute]
  rw [hcompiled]
  cases hleftDestination : lookup destinationLeft environment with
  | none =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_update environment
              (updateLoopLocal state.locals destinationLeft highValue)
              destinationRight lowValue
              (labelsIn_update environment state.locals destinationLeft highValue
                henvironment)
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_update (delete destinationRight environment)
              (updateLoopLocal state.locals destinationLeft highValue)
              destinationRight lowValue
              (labelsIn_delete_update_any environment state.locals destinationRight
                destinationLeft highValue henvironment)
  | some _ =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_update (delete destinationLeft environment)
              (updateLoopLocal state.locals destinationLeft highValue)
              destinationRight lowValue
              (labelsIn_delete_update_any environment state.locals destinationLeft
                destinationLeft highValue henvironment)
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_delete_update_any (delete destinationRight environment)
              (updateLoopLocal state.locals destinationLeft highValue)
              destinationLeft destinationRight lowValue
              (labelsIn_delete_update_any environment state.locals destinationRight
                destinationLeft highValue henvironment)

theorem comp_arith_longDiv_labelsIn
    (environment : LocationEnv) (locals : Nat → Option α)
    (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
    (henvironment : labelsIn environment locals) :
    (comp environment
      (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) : LoopProg α)).1 =
        .arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) ∧
      labelsIn
        (comp environment
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) : LoopProg α)).2
        locals := by
  have hcompiled :
      comp environment
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) : LoopProg α) =
        (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient),
          match lookup destinationLeft environment, lookup destinationRight environment with
          | none, none => environment
          | some _, none => delete destinationLeft environment
          | none, some _ => delete destinationRight environment
          | some _, some _ => delete destinationLeft (delete destinationRight environment)) := by
    simp [comp, compArith] <;> rfl
  rw [hcompiled]
  cases hleftDestination : lookup destinationLeft environment with
  | none =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · rfl
          · exact henvironment
      | some _ =>
          constructor
          · rfl
          · exact labelsIn_delete environment locals destinationRight henvironment
  | some _ =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · rfl
          · exact labelsIn_delete environment locals destinationLeft henvironment
      | some _ =>
          constructor
          · rfl
          · exact labelsIn_delete (delete destinationRight environment) locals destinationLeft
              (labelsIn_delete environment locals destinationRight henvironment)

theorem comp_arith_longDiv_full_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanCmp α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [Complement α]
    (longDiv : α → α → α → Option (α × α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
    (highValue lowValue divisorValue quotientValue remainderValue : α)
    (hhigh : state.locals sourceLeft = some highValue)
    (hlow : state.locals sourceRight = some lowValue)
    (hdivisor : state.locals quotient = some divisorValue)
    (hcompute : longDiv highValue lowValue divisorValue =
      some (quotientValue, remainderValue))
    (henvironment : labelsIn environment state.locals) :
    evalLoopProgFullWithLongDiv longDiv (fuel + 1) state
        (comp environment
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) :
            LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal
            (updateLoopLocal state.locals destinationRight remainderValue)
            destinationLeft quotientValue }) ∧
      labelsIn
        (comp environment
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) :
            LoopProg α)).2
        (updateLoopLocal
          (updateLoopLocal state.locals destinationRight remainderValue)
          destinationLeft quotientValue) := by
  have hcompiled :
      comp environment
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) :
            LoopProg α) =
        (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient),
          match lookup destinationLeft environment, lookup destinationRight environment with
          | none, none => environment
          | some _, none => delete destinationLeft environment
          | none, some _ => delete destinationRight environment
          | some _, some _ => delete destinationLeft (delete destinationRight environment)) := by
    simp [comp, compArith] <;> rfl
  have heval :
      evalLoopProgFullWithLongDiv longDiv (fuel + 1) state
          (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient)) =
        some (.normal { state with
          locals := updateLoopLocal
            (updateLoopLocal state.locals destinationRight remainderValue)
            destinationLeft quotientValue }) := by
    simp [evalLoopProgFullWithLongDiv, hhigh, hlow, hdivisor, hcompute]
  rw [hcompiled]
  cases hleftDestination : lookup destinationLeft environment with
  | none =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_update environment
              (updateLoopLocal state.locals destinationRight remainderValue)
              destinationLeft quotientValue
              (labelsIn_update environment state.locals destinationRight remainderValue
                henvironment)
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_update (delete destinationRight environment)
              (updateLoopLocal state.locals destinationRight remainderValue)
              destinationLeft quotientValue
              (labelsIn_delete_update_any environment state.locals destinationRight
                destinationRight remainderValue henvironment)
  | some _ =>
      cases hrightDestination : lookup destinationRight environment with
      | none =>
          constructor
          · exact heval
          · exact labelsIn_update (delete destinationLeft environment)
              (updateLoopLocal state.locals destinationRight remainderValue)
              destinationLeft quotientValue
              (labelsIn_delete_update_any environment state.locals destinationLeft
                destinationRight remainderValue henvironment)
      | some _ =>
          constructor
          · exact heval
          · exact labelsIn_delete_update_any (delete destinationRight environment)
              (updateLoopLocal state.locals destinationRight remainderValue)
              destinationLeft destinationLeft quotientValue
              (labelsIn_delete_update_any environment state.locals destinationRight
                destinationRight remainderValue henvironment)

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

theorem loopLookupFirst_of_mem
    (locals : Nat → Option α) (entries : List (Nat × α)) (name : Nat)
    (hmem : name ∈ entries.map Prod.fst) :
    ∃ value, loopLookupFirst locals entries name = some value := by
  induction entries with
  | nil =>
      simp at hmem
  | cons entry entries ih =>
      obtain ⟨entryName, entryValue⟩ := entry
      by_cases hsame : name = entryName
      · exact ⟨entryValue, by simp [loopLookupFirst, hsame]⟩
      · have htail : name ∈ entries.map Prod.fst := by
          simpa [hsame] using hmem
        obtain ⟨value, hvalue⟩ := ih htail
        exact ⟨value, by simp [loopLookupFirst, hsame, hvalue]⟩

theorem loopLookupFirst_not_mem
    (locals : Nat → Option α) (entries : List (Nat × α)) (name : Nat)
    (hmem : name ∉ entries.map Prod.fst) :
    loopLookupFirst locals entries name = locals name := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨entryName, entryValue⟩ := entry
      by_cases hsame : name = entryName
      · exact False.elim (hmem (by simp [hsame]))
      · have htail : name ∉ entries.map Prod.fst := by
          intro htail
          exact hmem (by simp [hsame, htail])
        simp [loopLookupFirst, hsame, ih htail]

theorem mem_zip_fst_iff
    (location : Nat) (destinations : List Nat) (values : List α)
    (hlength : destinations.length = values.length) :
    location ∈ (destinations.zip values).map Prod.fst ↔
      location ∈ destinations := by
  induction destinations generalizing values with
  | nil =>
      cases values with
      | nil => simp
      | cons value values => simp at hlength
  | cons destination destinations ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          simp only [List.length_cons] at hlength
          by_cases hsame : location = destination
          · simp [hsame]
          · have htail := ih (values := values) (by omega)
            simpa [hsame] using htail

theorem labelsIn_listDelete_zipUpdate
    (destinations : List Nat) (values : List α)
    (environment : LocationEnv) (locals : Nat → Option α)
    (hlength : destinations.length = values.length)
    (henvironment : labelsIn environment locals) :
    labelsIn (listDelete destinations environment)
      (loopLookupFirst locals (destinations.zip values)) := by
  intro name location hlookup
  have hlookup' :=
    lookup_of_listDelete destinations environment name location hlookup
  obtain ⟨oldValue, holdValue⟩ := henvironment name location hlookup'
  have hzip := mem_zip_fst_iff location destinations values hlength
  by_cases hdestination : location ∈ destinations
  · obtain ⟨value, hvalue⟩ :=
      loopLookupFirst_of_mem locals (destinations.zip values) location
        (hzip.mpr hdestination)
    exact ⟨value, hvalue⟩
  · have hnotzip : location ∉ (destinations.zip values).map Prod.fst := by
      intro hmem
      exact hdestination (hzip.mp hmem)
    have hvalue := loopLookupFirst_not_mem locals
      (destinations.zip values) location hnotzip
    exact ⟨oldValue, by rw [hvalue]; exact holdValue⟩

theorem comp_call_labelsIn
    (environment : LocationEnv)
    (returns : Option (List Nat × List Nat)) (target : Option Nat)
    (arguments : List Nat)
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
    (locals : Nat → Option α) (_henvironment : labelsIn environment locals) :
    (comp environment
      (.call returns target arguments handler) : LoopProg α × LocationEnv).1 =
        (match target with
        | some _ => .call returns target arguments handler
        | none =>
            match splitLast arguments with
            | none => .skip
            | some (pre, lastValue) =>
                match lookup lastValue environment with
                | none => .call returns none arguments handler
                | some destination => .call returns (some destination) pre handler) ∧
      labelsIn
    (comp environment
          (.call returns target arguments handler) : LoopProg α × LocationEnv).2
        locals := by
  have hnil : labelsIn ([] : LocationEnv) locals := by
    intro name source hlookup
    simp [lookup] at hlookup
  cases target with
  | some target =>
      constructor
      · simp [comp, compCall]
      · simpa [comp, compCall] using hnil
  | none =>
      cases harguments : splitLast arguments with
      | none =>
          constructor
          · simp [comp, compCall, harguments]
          · simpa [comp, compCall, harguments] using hnil
      | some pair =>
          obtain ⟨pre, lastValue⟩ := pair
          cases hlastValue : lookup lastValue environment with
          | none =>
              constructor
              · simp [comp, compCall, harguments, hlastValue]
              · simpa [comp, compCall, harguments, hlastValue] using hnil
          | some destination =>
              constructor
              · simp [comp, compCall, harguments, hlastValue]
              · simpa [comp, compCall, harguments, hlastValue] using hnil

theorem comp_call_target_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (returns : Option (List Nat × List Nat)) (target : Nat)
    (arguments : List Nat)
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
    (result : LoopResult α)
    (hcall : evalLoopCallWithCallsAndFfi functions ffiHandler fuel state
      returns (some target) arguments handler = some result) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (comp environment
          (.call returns (some target) arguments handler : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment
          (.call returns (some target) arguments handler : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment
          (.call returns (some target) arguments handler : LoopProg α) =
        (.call returns (some target) arguments handler, []) := by
    simp [comp, compCall]
  have heval :
      evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
          (.call returns (some target) arguments handler) =
        some result := by
    simpa [evalLoopProgWithCallsAndFfi] using hcall
  rw [hcompiled]
  constructor
  · exact heval
  · simp [labelsIn, lookup]

theorem comp_call_empty_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (returns : Option (List Nat × List Nat))
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat)) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (comp environment
          (.call returns none [] handler : LoopProg α)).1 =
        some (.normal state) ∧
      labelsIn
        (comp environment
          (.call returns none [] handler : LoopProg α)).2
        state.locals := by
  have hcompiled :
      comp environment
          (.call returns none [] handler : LoopProg α) =
        (.skip, []) := by
    simp [comp, compCall, splitLast]
  rw [hcompiled]
  constructor
  · simp [evalLoopProgWithCallsAndFfi, evalLoopProg]
  · simp [labelsIn, lookup]

theorem comp_call_implicit_target_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (returns : Option (List Nat × List Nat)) (arguments pre : List Nat)
    (lastValue destination : Nat)
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
    (result : LoopResult α)
    (hsplit : splitLast arguments = some (pre, lastValue))
    (hlookup : lookup lastValue environment = some destination)
    (hcall : evalLoopCallWithCallsAndFfi functions ffiHandler fuel state
      returns (some destination) pre handler = some result) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (comp environment
          (.call returns none arguments handler : LoopProg α)).1 =
        some result ∧
      labelsIn
        (comp environment
          (.call returns none arguments handler : LoopProg α)).2
        (loopResultState result).locals := by
  have hcompiled :
      comp environment
          (.call returns none arguments handler : LoopProg α) =
        (.call returns (some destination) pre handler, []) := by
    simp [comp, compCall, hsplit, hlookup]
  have heval :
      evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
          (.call returns (some destination) pre handler) =
        some result := by
    simpa [evalLoopProgWithCallsAndFfi] using hcall
  rw [hcompiled]
  constructor
  · exact heval
  · simp [labelsIn, lookup]

theorem comp_call_unresolved_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (returns : Option (List Nat × List Nat)) (arguments pre : List Nat)
    (lastValue : Nat)
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
    (hsplit : splitLast arguments = some (pre, lastValue))
    (hlookup : lookup lastValue environment = none) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (comp environment
          (.call returns none arguments handler : LoopProg α)).1 =
        none ∧
      labelsIn
        (comp environment
          (.call returns none arguments handler : LoopProg α)).2
        state.locals := by
  have hcompiled :
      comp environment
          (.call returns none arguments handler : LoopProg α) =
        (.call returns none arguments handler, []) := by
    simp [comp, compCall, hsplit, hlookup]
  have heval :
      evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
          (.call returns none arguments handler) = none := by
    cases fuel <;> cases returns <;> cases handler <;>
      simp [evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi]
  rw [hcompiled]
  constructor
  · exact heval
  · simp [labelsIn, lookup]

theorem comp_ffi_labelsIn
    (environment : LocationEnv)
    (function : FunName) (configuration configurationLength array arrayLength : Nat)
    (live : List Nat) (locals : Nat → Option α)
    (_henvironment : labelsIn environment locals) :
    (comp environment
      (.ffi function configuration configurationLength array arrayLength live) :
        LoopProg α × LocationEnv).1 =
        .ffi function configuration configurationLength array arrayLength live ∧
      labelsIn
        (comp environment
          (.ffi function configuration configurationLength array arrayLength live) :
            LoopProg α × LocationEnv).2
        locals := by
  constructor
  · simp [comp]
  · simp [comp, labelsIn, lookup]

theorem comp_ffi_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (function : FunName) (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (resultState : LoopState α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength : state.locals configurationLength =
      some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffiHandler function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some resultState) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (comp environment
          (.ffi function configuration configurationLength array arrayLength live :
            LoopProg α)).1 =
        some (.normal resultState) ∧
      labelsIn
        (comp environment
          (.ffi function configuration configurationLength array arrayLength live :
            LoopProg α)).2
        resultState.locals := by
  have hcompiled :
      comp environment
          (.ffi function configuration configurationLength array arrayLength live :
            LoopProg α) =
        (.ffi function configuration configurationLength array arrayLength live, []) := by
    simp [comp]
  have heval :
      evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal resultState) := by
    simp [evalLoopProgWithCallsAndFfi, hconfiguration, hconfigurationLength,
      harray, harrayLength, hffi]
  rw [hcompiled]
  constructor
  · exact heval
  · simp [labelsIn, lookup]

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

theorem comp_primitive_single_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : LoopPrimitiveHandler α)
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (destination : Nat) (operator : PrimOp) (arguments : List Nat)
    (argumentValues : List α) (value : α)
    (harguments : loopReadLocals state.locals arguments = some argumentValues)
    (hprimitive : primitive operator argumentValues = some [value])
    (henvironment : labelsIn environment state.locals) :
    evalLoopProgWithPrimitive primitive (fuel + 1) state
        (comp environment
          (.primitive [destination] operator arguments : LoopProg α)).1 =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) ∧
      labelsIn
        (comp environment
          (.primitive [destination] operator arguments : LoopProg α)).2
        (updateLoopLocal state.locals destination value) := by
  have hcompiled :
      comp environment
          (.primitive [destination] operator arguments : LoopProg α) =
        (.primitive [destination] operator arguments,
          listDelete [destination] environment) := by
    simp [comp]
  have heval :
      evalLoopProgWithPrimitive primitive (fuel + 1) state
          (.primitive [destination] operator arguments) =
        some (.normal { state with
          locals := updateLoopLocal state.locals destination value }) := by
    simp [evalLoopProgWithPrimitive, harguments, hprimitive,
      loopAssignValues, loopLookupFirst_singleton]
  rw [hcompiled]
  constructor
  · exact heval
  · simpa [listDelete, loopLookupFirst_singleton] using
      (labelsIn_delete_update environment state.locals destination value
        henvironment)

theorem comp_primitive_general_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : LoopPrimitiveHandler α)
    (environment : LocationEnv) (state : LoopState α) (fuel : Nat)
    (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
    (argumentValues values : List α)
    (harguments : loopReadLocals state.locals arguments = some argumentValues)
    (hprimitive : primitive operator argumentValues = some values)
    (hlength : destinations.length = values.length)
    (henvironment : labelsIn environment state.locals) :
    evalLoopProgWithPrimitive primitive (fuel + 1) state
        (comp environment
          (.primitive destinations operator arguments : LoopProg α)).1 =
        some (.normal { state with
          locals := loopLookupFirst state.locals (destinations.zip values) }) ∧
      labelsIn
        (comp environment
          (.primitive destinations operator arguments : LoopProg α)).2
        (loopLookupFirst state.locals (destinations.zip values)) := by
  have hcompiled :
      comp environment
          (.primitive destinations operator arguments : LoopProg α) =
        (.primitive destinations operator arguments,
          listDelete destinations environment) := by
    simp [comp]
  have heval :
      evalLoopProgWithPrimitive primitive (fuel + 1) state
          (.primitive destinations operator arguments) =
        some (.normal { state with
          locals := loopLookupFirst state.locals (destinations.zip values) }) := by
    simp [evalLoopProgWithPrimitive, harguments, hprimitive,
      loopAssignValues, hlength]
  rw [hcompiled]
  constructor
  · exact heval
  · exact labelsIn_listDelete_zipUpdate destinations values environment
      state.locals hlength henvironment

end LoopCall
end Flapjack
