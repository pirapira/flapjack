import Flapjack.CrepeCorrectness

/-!
Source-to-Crep simulation relations.

The original CakeML proof is driven by a relation between structured Pancake
locals and flattened Crep locals.  This module gives the corresponding Lean
interface before the induction over programs is assembled.  The current
front-end subset has no compiled global environment, so the state relation
explicitly records the supported empty-global condition; global lowering can
later relax that component without changing the control-result relation.
-/

namespace Flapjack

def readCrepLocals {α : Type u} (locals : Nat → Option α) :
    List Nat → Option (List α)
  | [] => some []
  | name :: names => do
      let value ← locals name
      let values ← readCrepLocals locals names
      pure (value :: values)

theorem readCrepLocals_some_defined
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (hread : readCrepLocals locals names = some values) :
    ∀ name, name ∈ names → (locals name).isSome = true := by
  induction names generalizing values with
  | nil =>
      simp
  | cons head names ih =>
      cases hvalue : locals head with
      | none =>
          simp [readCrepLocals, hvalue] at hread
      | some value =>
          cases hvalues : readCrepLocals locals names with
          | none =>
              simp [readCrepLocals, hvalue, hvalues] at hread
          | some tailValues =>
              simp [readCrepLocals, hvalue, hvalues] at hread
              intro name hname
              have hname' : name = head ∨ name ∈ names := by
                simpa [List.mem_cons] using hname
              rcases hname' with heq | htail
              · have hlocal : locals name = some value := by
                  simpa [heq] using hvalue
                simp [hlocal]
              · exact ih tailValues hvalues name htail

theorem readCrepLocals_length
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (hread : readCrepLocals locals names = some values) :
    values.length = names.length := by
  induction names generalizing values with
  | nil =>
      simp [readCrepLocals] at hread
      cases hread
      rfl
  | cons head names ih =>
      cases hvalue : locals head with
      | none =>
          simp [readCrepLocals, hvalue] at hread
      | some value =>
          cases hvalues : readCrepLocals locals names with
          | none =>
              simp [readCrepLocals, hvalue, hvalues] at hread
          | some tailValues =>
              simp [readCrepLocals, hvalue, hvalues] at hread
              subst values
              have htail := ih tailValues hvalues
              simp [htail]

def panValueCrepValuesRel {α : Type u}
    (sourceValues : List (PanValue α)) (crepValues : List α) : Prop :=
  crepValues = sourceValues.flatMap panValueFlatWords

def panValueCrepLocalsRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α) : Prop :=
  ∀ name value shape slots,
    sourceLocals name = some value →
    lookupInfo name context.vars = some (shape, slots) →
      panShapeMatches (panValueShape structs value) shape = true ∧
      readCrepLocals crepLocals slots = some (panValueFlatWords value)

theorem panValueCrepLocalsRel_lookup_evidence
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (value : PanValue α)
    (shape : Shape) (slots : List Nat)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hsource : sourceLocals name = some value)
    (hlookup : lookupInfo name context.vars = some (shape, slots)) :
    panShapeMatches (panValueShape structs value) shape = true ∧
      slots.length = (panValueFlatWords value).length ∧
      readCrepLocals crepLocals slots = some (panValueFlatWords value) := by
  have hevidence := hrel name value shape slots hsource hlookup
  exact ⟨hevidence.1, (readCrepLocals_length crepLocals slots
    (panValueFlatWords value) hevidence.2).symm, hevidence.2⟩

/-! Cake's `locals_rel_wf_shape` (`pan_to_crepProofScript.sml:2345`)
    transports the well-formed source-value shape through a related local.
    The current Flapjack relation records the compiled shape match but keeps
    value well-formedness as an explicit premise, so named-structure contexts
    remain visible at this boundary. -/
theorem panValueCrepLocalsRel_wf_shape
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (value : PanValue α)
    (shape : Shape) (slots : List Nat)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hsource : sourceLocals name = some value)
    (hlookup : lookupInfo name context.vars = some (shape, slots))
    (hvalue : panValueIsWf structs value = true) :
    panShapeMatches (panValueShape structs value) shape = true ∧
      isWfShape structs (panValueShape structs value) = true := by
  have hevidence := panValueCrepLocalsRel_lookup_evidence structs context
    sourceLocals crepLocals name value shape slots hrel hsource hlookup
  exact ⟨hevidence.1, panValueIsWf_isWfShape_panValueShape structs value hvalue⟩

def panValueCrepMemoryRel {α : Type u}
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) : Prop :=
  panValueWordMemory sourceMemory = crepMemory

def panValueCrepMemoryRelExcept {α : Type u}
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) (excluded : α → Prop) : Prop :=
  ∀ address, ¬ excluded address →
    panValueWordMemory sourceMemory address = crepMemory address

theorem panValueCrepMemoryRelExcept_update_word
    [BEq α] [LawfulBEq α]
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) (address value : α)
    (excluded : α → Prop)
    (hrel : panValueCrepMemoryRelExcept sourceMemory crepMemory excluded) :
    panValueCrepMemoryRelExcept
      (updatePanValueMemory sourceMemory address (.word value))
      (updateMemory crepMemory address value) excluded := by
  intro current hnot
  by_cases hcurrent : current == address
  · simp [panValueWordMemory, updatePanValueMemory,
      updatePanValueMap, updateMemory, hcurrent]
  · simpa [panValueWordMemory, updatePanValueMemory,
      updatePanValueMap, updateMemory, hcurrent] using hrel current hnot

theorem panValueCrepMemoryRelExcept_update_crep_at_excluded
    [BEq α] [LawfulBEq α]
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) (address value : α)
    (excluded : α → Prop)
    (hrel : panValueCrepMemoryRelExcept sourceMemory crepMemory excluded)
    (hexcluded : excluded address) :
    panValueCrepMemoryRelExcept sourceMemory
      (updateMemory crepMemory address value) excluded := by
  intro current hnot
  by_cases hcurrent : current == address
  · have heq : current = address := by simpa using hcurrent
    exact False.elim (hnot (by simpa [heq] using hexcluded))
  · simpa [updateMemory, hcurrent] using hrel current hnot

def panValueCrepStateRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) : Prop :=
  sourceGlobals = (fun _ => none) ∧
  panValueCrepLocalsRel structs context sourceLocals crepState.locals ∧
  panValueCrepMemoryRel sourceMemory crepState.memory

/-! Cake's `state_rel_globals` (`pan_to_crepProofScript.sml:71-75`): the
    source-global component of a related state is empty.  Flapjack keeps the
    struct context explicit (and therefore does not impose Cake's initial
    empty-struct assumption), but this global projection is unchanged. -/
theorem panValueCrepStateRel_sourceGlobals_eq_none
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState) :
    sourceGlobals = (fun _ => none) :=
  hrel.1

/-! Cake's `state_rel` carries ordinary memory unchanged.  This lookup form is
    the state/evaluator bridge needed by expression and clocked-call cases:
    only a source word is readable as a Crep word, and the related target state
    must expose that same value at the address. -/
theorem panValueCrepStateRel_memory_lookup
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (address value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState)
    (hmemory : sourceMemory address = some (.word value)) :
    crepState.memory address = some value := by
  have hword : panValueWordMemory sourceMemory address = some value := by
    simp [panValueWordMemory, hmemory]
  have hstate := congrFun hrel.2.2 address
  rw [hword] at hstate
  exact hstate.symm

theorem panValueCrepLocalsRel_word_slot
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hsource : sourceLocals name = some (.word value))
    (hlookup : lookupInfo name context.vars = some (.one, [slot])) :
    crepLocals slot = some value := by
  have hread := (hrel name (.word value) .one [slot] hsource hlookup).2
  simp [readCrepLocals, panValueFlatWords, panValueFlatWordsFuel] at hread
  cases hlocal : crepLocals slot with
  | none => simp [hlocal] at hread
  | some current =>
      simp [hlocal] at hread
      simp [hread]

theorem panValueCrepLocalsRel_defined
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (value : PanValue α) (shape : Shape) (slots : List Nat)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hsource : sourceLocals name = some value)
    (hlookup : lookupInfo name context.vars = some (shape, slots)) :
    ∀ slot, slot ∈ slots → (crepLocals slot).isSome = true := by
  apply readCrepLocals_some_defined crepLocals slots _
  exact (hrel name value shape slots hsource hlookup).2

/-! A state relation that tolerates compiler-owned memory locations.  This is
needed after a raised callee has written its flattened payload to the Crep
return area and a caller handler continues execution. -/
def panValueCrepStateRelExcept {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) (excluded : α → Prop) : Prop :=
  sourceGlobals = (fun _ => none) ∧
  panValueCrepLocalsRel structs context sourceLocals crepState.locals ∧
  panValueCrepMemoryRelExcept sourceMemory crepState.memory excluded

theorem panValueCrepStateRelExcept_of_state_rel
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (excluded : α → Prop)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
      sourceMemory state excluded := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro address _
  exact congrFun hrel.2.2 address

theorem panValueCrepStateRelExcept_update_crep_at_excluded
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (address value : α) (excluded : α → Prop)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) (hexcluded : excluded address) :
    panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
      sourceMemory { state with memory := updateMemory state.memory address value }
      excluded := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  have hexcept := panValueCrepStateRelExcept_of_state_rel structs context
    sourceLocals sourceGlobals sourceMemory state excluded hrel
  exact panValueCrepMemoryRelExcept_update_crep_at_excluded
    sourceMemory state.memory address value excluded
    hexcept.2.2 hexcluded

def panValueCrepRaisedStateRelExcept {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) (excluded : α → Prop) : Prop :=
  sourceGlobals = (fun _ => none) ∧
  panValueCrepLocalsRel structs context (fun _ => none) crepState.locals ∧
  panValueCrepMemoryRelExcept sourceMemory crepState.memory excluded

def panValueCrepRaisedStateRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) (spillAddress : α) : Prop :=
  panValueCrepRaisedStateRelExcept structs context sourceGlobals sourceMemory
    crepState (fun address => address = spillAddress)

def panValueCrepRaisedControlRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (crepState : CrepState α) (exceptionCode spillAddress : α) : Prop :=
  panValueCrepRaisedStateRel structs context sourceGlobals sourceMemory
    crepState spillAddress ∧
  exceptionRel sourceException sourceValue exceptionCode

theorem panValueCrepRaisedStateRel_global_spill
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (spillAddress value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepRaisedStateRel structs context sourceGlobals sourceMemory
      { state with globals := updateMemory state.globals spillAddress value }
      spillAddress := by
  have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
      state.locals := by
    intro name currentValue shape slots hsource _
    simp at hsource
  refine ⟨hrel.1, hlocals, ?_⟩
  intro address _
  exact congrFun hrel.2.2 address

/-! The global-aware evaluator stores the reserved exception payload in the
    global area.  This companion relation keeps the existing memory relation
    intact while making the global spill observable to its callers. -/
def panValueCrepRaisedGlobalSpillRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (value : α)
    (crepState : CrepState α) (spillAddress : α) : Prop :=
  panValueCrepRaisedStateRel structs context sourceGlobals sourceMemory
    crepState spillAddress ∧
  crepState.globals spillAddress = some value ∧
  sourceValue = .word value

theorem panValueCrepRaisedGlobalSpillRel_word
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (spillAddress value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepRaisedGlobalSpillRel structs context sourceGlobals sourceMemory
      (.word value) value
      { state with globals := updateMemory state.globals spillAddress value }
      spillAddress := by
  have hstate := panValueCrepRaisedStateRel_global_spill
    structs context sourceLocals sourceGlobals sourceMemory state
    spillAddress value hrel
  refine ⟨hstate, ?_, rfl⟩
  simp [updateMemory]

def panValueCrepControlRel {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α) : Prop :=
  match sourceResult, crepResult with
  | .normal sourceLocals sourceGlobals sourceMemory,
      .normal crepState =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | .returned sourceLocals sourceGlobals sourceMemory sourceValues,
      .returned crepState crepValues =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory crepState ∧
      panValueCrepValuesRel sourceValues crepValues
  | .raised _sourceLocals sourceGlobals sourceMemory exception value,
      .raised crepState exceptionCode =>
      ∃ spillAddress,
        panValueCrepRaisedControlRel structs context exceptionRel
          sourceGlobals sourceMemory exception value crepState exceptionCode
            spillAddress
  | .broke sourceLocals sourceGlobals sourceMemory, .broke crepState _ =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | .continued sourceLocals sourceGlobals sourceMemory, .continued crepState _ =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | _, _ => False

def panValueCrepRaisedControlRelExcept {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (crepState : CrepState α) (exceptionCode : α)
    (excluded : α → Prop) : Prop :=
  panValueCrepRaisedStateRelExcept structs context sourceGlobals sourceMemory
    crepState excluded ∧
  exceptionRel sourceException sourceValue exceptionCode

/-! Control results after a handler may still carry the callee's reserved
payload spill.  The ordinary relation remains exact-memory; this companion
relation makes the owned locations explicit for normal and returned handler
results as well. -/
def panValueCrepControlRelExcept {α : Type u}
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α) (excluded : α → Prop) : Prop :=
  match sourceResult, crepResult with
  | .normal sourceLocals sourceGlobals sourceMemory,
      .normal crepState =>
      panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
        sourceMemory crepState excluded
  | .returned sourceLocals sourceGlobals sourceMemory sourceValues,
      .returned crepState crepValues =>
      panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
        sourceMemory crepState excluded ∧
      panValueCrepValuesRel sourceValues crepValues
  | .raised _sourceLocals sourceGlobals sourceMemory exception value,
      .raised crepState exceptionCode =>
      panValueCrepRaisedControlRelExcept structs context exceptionRel
        sourceGlobals sourceMemory exception value crepState exceptionCode
        excluded
  | .broke sourceLocals sourceGlobals sourceMemory, .broke crepState _ =>
      panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
        sourceMemory crepState excluded
  | .continued sourceLocals sourceGlobals sourceMemory, .continued crepState _ =>
      panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
        sourceMemory crepState excluded
  | _, _ => False

theorem panValueCrepRaisedStateRel_word_spill
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (spillAddress value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepRaisedStateRel structs context sourceGlobals sourceMemory
      { state with memory := updateMemory state.memory spillAddress value }
      spillAddress := by
  have hmemory : panValueCrepMemoryRel sourceMemory state.memory := hrel.2.2
  have hexcept : panValueCrepMemoryRelExcept sourceMemory state.memory
      (fun address => address = spillAddress) := by
    intro address _
    exact congrFun (show panValueWordMemory sourceMemory = state.memory
      from hmemory) address
  have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
      state.locals := by
    intro name currentValue shape slots hsource _
    simp at hsource
  exact ⟨hrel.1, hlocals,
    panValueCrepMemoryRelExcept_update_crep_at_excluded sourceMemory
      state.memory spillAddress value (fun address => address = spillAddress)
      hexcept rfl⟩

theorem panValueCrepRaisedStateRel_two_word_spill
    [BEq α] [LawfulBEq α] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (spillAddress stride left right : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepRaisedStateRelExcept structs context sourceGlobals sourceMemory
      { locals := state.locals
        memory := updateMemory (updateMemory state.memory spillAddress left)
          (spillAddress + stride) right }
      (fun address => address = spillAddress ∨ address = spillAddress + stride) := by
  have hmemory : panValueCrepMemoryRel sourceMemory state.memory := hrel.2.2
  have hexcept : panValueCrepMemoryRelExcept sourceMemory state.memory
      (fun address => address = spillAddress ∨ address = spillAddress + stride) := by
    intro address _
    exact congrFun (show panValueWordMemory sourceMemory = state.memory
      from hmemory) address
  have hfirst := panValueCrepMemoryRelExcept_update_crep_at_excluded
    sourceMemory state.memory spillAddress left
      (fun address => address = spillAddress ∨ address = spillAddress + stride)
      hexcept (Or.inl rfl)
  have hsecond := panValueCrepMemoryRelExcept_update_crep_at_excluded
    sourceMemory (updateMemory state.memory spillAddress left)
      (spillAddress + stride) right
      (fun address => address = spillAddress ∨ address = spillAddress + stride)
      hfirst (Or.inr rfl)
  have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
      state.locals := by
    intro name currentValue shape slots hsource _
    simp at hsource
  exact ⟨hrel.1, hlocals, hsecond⟩

theorem panValueCrepValuesRel_singleton (value : PanValue α) :
    panValueCrepValuesRel [value] (panValueFlatWords value) := by
  simp [panValueCrepValuesRel]

theorem panValueCrepLocalsRel_empty
    (structs : StructContext) (context : CompileContext α)
    (crepLocals : Nat → Option α) :
    panValueCrepLocalsRel structs context (fun _ => none) crepLocals := by
  intro name value shape slots hsource _
  simp at hsource

theorem panValueCrepMemoryRel_def
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) :
    panValueCrepMemoryRel sourceMemory crepMemory ↔
      panValueWordMemory sourceMemory = crepMemory := by
  rfl

theorem panValueCrepMemoryRel_update_word
    [BEq α] [LawfulBEq α]
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α) (address value : α)
    (hrel : panValueCrepMemoryRel sourceMemory crepMemory) :
    panValueCrepMemoryRel
      (updatePanValueMemory sourceMemory address (.word value))
      (updateMemory crepMemory address value) := by
  change panValueWordMemory sourceMemory = crepMemory at hrel
  funext current
  by_cases hcurrent : current == address
  · simp [panValueWordMemory,
      updatePanValueMemory, updatePanValueMap, updateMemory, hcurrent]
  · simpa [panValueWordMemory, updatePanValueMemory,
      updatePanValueMap, updateMemory, hcurrent] using congrFun hrel current

theorem panValueCrepLocalsRel_extend
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceLocals' : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α)
    (hsource : sourceLocals' = updatePanValueMap sourceLocals name value)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hread : readCrepLocals crepLocals slots = some (panValueFlatWords value))
    (hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals crepLocals oldSlots = some (panValueFlatWords oldValue)) :
    panValueCrepLocalsRel structs
      { context with vars := (name, (shape, slots)) :: context.vars }
      sourceLocals' crepLocals := by
  intro current currentValue currentShape currentSlots hcurrent hlookup
  by_cases hname : current = name
  · subst current
    have hlookup' : some (shape, slots) =
        some (currentShape, currentSlots) := by
      simpa [lookupInfo] using hlookup
    have hpair : (shape, slots) = (currentShape, currentSlots) :=
      Option.some.inj hlookup'
    have hshapeEq : shape = currentShape := congrArg Prod.fst hpair
    have hslotsEq : slots = currentSlots := congrArg Prod.snd hpair
    cases hshapeEq
    cases hslotsEq
    rw [hsource] at hcurrent
    simp [updatePanValueMap] at hcurrent
    cases hcurrent
    exact And.intro hshape hread
  · have hlookupOld : lookupInfo current context.vars =
        some (currentShape, currentSlots) := by
      simpa [lookupInfo, hname, Ne.symm hname] using hlookup
    have hcurrentOld : sourceLocals current = some currentValue := by
      rw [hsource] at hcurrent
      simpa [updatePanValueMap, hname] using hcurrent
    exact hold current currentValue currentShape currentSlots hname
      hcurrentOld hlookupOld

theorem readCrepLocals_update_of_not_mem
    (locals : Nat → Option α) (slot : Nat) (value : α) :
    ∀ slots, slot ∉ slots →
      readCrepLocals (updateCrepLocal locals slot value) slots =
        readCrepLocals locals slots := by
  intro slots hnot
  induction slots with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ≠ slot := by
        intro heq
        apply hnot
        simp [heq]
      have htail : slot ∉ tail := by
        intro hmem
        apply hnot
        simp [hmem]
      simp [readCrepLocals, updateCrepLocal, hhead,
        ih htail]

theorem panValueCrepLocalsRel_update_word
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    panValueCrepLocalsRel structs context
      (updatePanValueMap sourceLocals name (.word value))
      (updateCrepLocal crepLocals slot value) := by
  intro current currentValue currentShape currentSlots hcurrent hcurrentLookup
  by_cases hname : current = name
  · subst current
    have hpair : (Shape.one, [slot]) = (currentShape, currentSlots) := by
      have hlookup' : some (Shape.one, [slot]) =
          some (currentShape, currentSlots) := by
        simpa [hlookup] using hcurrentLookup
      exact Option.some.inj hlookup'
    have hshape : currentShape = Shape.one := (congrArg Prod.fst hpair).symm
    have hslots : currentSlots = [slot] := (congrArg Prod.snd hpair).symm
    cases hshape
    cases hslots
    have hvalue : currentValue = PanValue.word value := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    constructor
    · simp [panValueShape, panShapeMatches]
    · simp [readCrepLocals, updateCrepLocal, panValueFlatWords,
        panValueFlatWordsFuel]
  · have hcurrentOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hname] using hcurrent
    have hold := hrel current currentValue currentShape currentSlots
      hcurrentOld hcurrentLookup
    have hnot : slot ∉ currentSlots :=
      hnoalias current currentShape currentSlots hname hcurrentLookup
    exact ⟨hold.1,
      (readCrepLocals_update_of_not_mem crepLocals slot value currentSlots hnot).symm ▸ hold.2⟩

theorem lookupCompiledFunction_compileFunctions_head
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α)
    (declarations : List (Decl α)) :
    lookupCompiledFunction declaration.name
      (compileFunctions context (.function declaration :: declarations)) =
      some ((compileParamVars declaration.params 0).2.1,
        compileProg
          { context with
              vars := panToCrepMakeVmap declaration.params
              maxVar := (compileParamVars declaration.params 0).2.2 }
          declaration.body) := by
  simp [compileFunctions, compileFunDecl, panToCrepMakeVmap,
    lookupCompiledFunction]

end Flapjack
