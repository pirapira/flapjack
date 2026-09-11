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
              vars := (compileParamVars declaration.params 0).1
              maxVar := (compileParamVars declaration.params 0).2.2 }
          declaration.body) := by
  simp [compileFunctions, compileFunDecl, lookupCompiledFunction]

end Flapjack
