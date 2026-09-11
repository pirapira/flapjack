import Flapjack.CrepeCalleeParameterListGeneralRelation

/-!
Append-order callee-entry transport.

`compileParamVars` stores formal parameter metadata in source order, whereas
the one-entry context extension is naturally expressed as a list append.  The
lookup lemmas here make that order explicit and preserve the existing
source-to-Crep relation for old bindings.
-/

namespace Flapjack

def addCalleeParameterContextAppend (context : CompileContext α)
    (parameter : CalleeParameter α) : CompileContext α :=
  { context with
      vars := context.vars ++ [(parameter.name, (parameter.shape, parameter.slots))] }

def foldCalleeParameterContextAppend (context : CompileContext α)
    (parameters : List (CalleeParameter α)) : CompileContext α :=
  parameters.foldl addCalleeParameterContextAppend context

def CalleeParameterListFreshAppend [BEq String]
    (structs : StructContext) (context : CompileContext α) :
    List (CalleeParameter α) → Prop
  | [] => True
  | parameter :: parameters =>
      lookupInfo parameter.name context.vars = none ∧
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true ∧
      parameter.slots.length = parameter.values.length ∧
      CrepDistinctNames parameter.slots ∧
      panValueFlatWords parameter.value = parameter.values ∧
      (∀ oldName oldShape oldSlots,
        oldName ≠ parameter.name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        ∀ slot ∈ parameter.slots, slot ∉ oldSlots) ∧
      CalleeParameterListFreshAppend structs
        (addCalleeParameterContextAppend context parameter) parameters

theorem calleeParameterListFreshAppend_length
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (parameters : List (CalleeParameter α))
    (hfresh : CalleeParameterListFreshAppend structs context parameters) :
    ∀ parameter ∈ parameters,
      parameter.slots.length = parameter.values.length := by
  induction parameters generalizing context with
  | nil =>
      intro parameter hparameter
      simp at hparameter
  | cons parameter parameters ih =>
      rcases hfresh with ⟨hname, hshape, hlength, hdistinct, hflat, hnoalias, htail⟩
      intro current hcurrent
      simp only [List.mem_cons] at hcurrent
      rcases hcurrent with rfl | hcurrent
      · exact hlength
      · exact ih (context := addCalleeParameterContextAppend context parameter)
          htail current hcurrent

theorem lookupInfo_append_of_ne
    [LawfulBEq String]
    (entries : InfoMap β) (name newName : String) (value : β)
    (hne : name ≠ newName) :
    lookupInfo name (entries ++ [(newName, value)]) = lookupInfo name entries := by
  induction entries with
  | nil => simp [lookupInfo, Ne.symm hne]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, candidateValue⟩
      by_cases hcandidate : candidate = name
      · subst candidate
        simp [lookupInfo]
      · simp [lookupInfo, hcandidate, ih]

theorem lookupInfo_append_new
    [LawfulBEq String]
    (entries : InfoMap β) (name : String) (value : β)
    (hnone : lookupInfo name entries = none) :
    lookupInfo name (entries ++ [(name, value)]) = some value := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, candidateValue⟩
      by_cases hcandidate : candidate = name
      · subst candidate
        simp [lookupInfo] at hnone
      · simp [lookupInfo, hcandidate] at hnone ⊢
        exact ih hnone

theorem panValueCrepStateRel_add_parameter_append_fresh
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (parameter : CalleeParameter α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hname : lookupInfo parameter.name context.vars = none)
    (hshape : panShapeMatches (panValueShape structs parameter.value)
      parameter.shape = true)
    (hlength : parameter.slots.length = parameter.values.length)
    (hdistinct : CrepDistinctNames parameter.slots)
    (hflat : panValueFlatWords parameter.value = parameter.values)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ parameter.name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ parameter.slots, slot ∉ oldSlots) :
    panValueCrepStateRel structs
      (addCalleeParameterContextAppend context parameter)
      (updatePanValueMap sourceLocals parameter.name parameter.value)
      sourceGlobals sourceMemory
      { state with
          locals := updateCrepLocalList state.locals parameter.slots parameter.values } := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro current currentValue currentShape currentSlots hcurrent hlookup
  by_cases hcurrentName : current = parameter.name
  · subst current
    have hnew := lookupInfo_append_new context.vars parameter.name
      (parameter.shape, parameter.slots) hname
    have hpair : (parameter.shape, parameter.slots) =
        (currentShape, currentSlots) := by
      exact Option.some.inj (hnew.symm.trans hlookup)
    have hshape' : currentShape = parameter.shape :=
      (congrArg Prod.fst hpair).symm
    have hslots' : currentSlots = parameter.slots :=
      (congrArg Prod.snd hpair).symm
    cases hshape'
    cases hslots'
    have hvalue : currentValue = parameter.value := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    have hread := readCrepLocals_updateCrepLocalList state.locals
      parameter.slots parameter.values hlength hdistinct
    exact ⟨hshape, by simpa [hflat] using hread⟩
  · have hsourceOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hcurrentName] using hcurrent
    have hlookupOld : lookupInfo current context.vars =
        some (currentShape, currentSlots) := by
      have hlookup' := lookupInfo_append_of_ne context.vars current
        parameter.name (parameter.shape, parameter.slots) hcurrentName
      exact hlookup'.symm ▸ hlookup
    have hold := hrel.2.1 current currentValue currentShape currentSlots
      hsourceOld hlookupOld
    have hnot : ∀ slot ∈ parameter.slots, slot ∉ currentSlots :=
      hnoalias current currentShape currentSlots hcurrentName hlookupOld
    have hread := readCrepLocals_updateCrepLocalList_of_not_mem state.locals
      parameter.slots parameter.values currentSlots hlength hnot
    exact ⟨hold.1, hread.symm ▸ hold.2⟩

theorem panValueCrepStateRel_add_parameters_append_fresh
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (parameters : List (CalleeParameter α))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hfresh : CalleeParameterListFreshAppend structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContextAppend context parameters)
      (foldCalleeParameterSource sourceLocals parameters) sourceGlobals
      sourceMemory
      { state with locals := foldCalleeParameterLocals state.locals parameters } := by
  induction parameters generalizing context sourceLocals state with
  | nil =>
      simpa [foldCalleeParameterContextAppend, foldCalleeParameterSource,
        foldCalleeParameterLocals] using hrel
  | cons parameter parameters ih =>
      rcases hfresh with ⟨hname, hshape, hlength, hdistinct, hflat, hnoalias, htail⟩
      have hstep := panValueCrepStateRel_add_parameter_append_fresh
        structs context sourceLocals sourceGlobals sourceMemory state parameter hrel
        hname hshape hlength hdistinct hflat hnoalias
      have hrest := ih
        (context := addCalleeParameterContextAppend context parameter)
        (sourceLocals := updatePanValueMap sourceLocals parameter.name parameter.value)
        (state := { state with
          locals := updateCrepLocalList state.locals parameter.slots parameter.values })
        hstep htail
      simpa [foldCalleeParameterContextAppend, foldCalleeParameterSource,
        foldCalleeParameterLocals, addCalleeParameterContextAppend] using hrest

theorem panValueCrepCalleeStateRel_parameters_append
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hfresh : CalleeParameterListFreshAppend structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContextAppend context parameters)
      (foldCalleeParameterSource (fun _ => none) parameters) sourceGlobals
      sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none) parameters,
        memory := crepMemory } := by
  have hrel : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { locals := (fun _ => none), memory := crepMemory } := by
    refine ⟨hglobals, panValueCrepLocalsRel_empty structs context (fun _ => none), ?_⟩
    exact hmemory
  exact panValueCrepStateRel_add_parameters_append_fresh structs context
    (fun _ => none) sourceGlobals sourceMemory
    { locals := (fun _ => none), memory := crepMemory }
    parameters hrel hfresh

theorem panValueCrepCalleeStateRel_parameters_append_of_bind_assign
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (calleeLocals : VarName → Option (PanValue α))
    (targetCalleeLocals : Nat → Option α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hbind : bindPanValueParameters (parameters.map CalleeParameter.name)
        (parameters.map CalleeParameter.value) = some calleeLocals)
    (hassign : assignCrepValues (fun _ => none)
        (parameters.flatMap CalleeParameter.slots)
        (parameters.flatMap CalleeParameter.values) = some targetCalleeLocals)
    (hfresh : CalleeParameterListFreshAppend structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContextAppend context parameters) calleeLocals sourceGlobals
      sourceMemory
      { locals := targetCalleeLocals, memory := crepMemory } := by
  have hbound := bindPanValueParameters_parameters parameters
  have hcallee : calleeLocals = foldCalleeParameterSource
      (fun _ => none) parameters := by
    exact Option.some.inj (hbind.symm.trans hbound)
  have hlength := calleeParameterListFreshAppend_length structs context parameters hfresh
  have hassigned := assignCrepValues_parameters parameters hlength
  have htarget : targetCalleeLocals = foldCalleeParameterLocals
      (fun _ => none) parameters := by
    exact Option.some.inj (hassign.symm.trans hassigned)
  have hrel := panValueCrepCalleeStateRel_parameters_append structs context
    sourceGlobals sourceMemory crepMemory parameters hglobals hmemory hfresh
  simpa [hcallee, htarget] using hrel

end Flapjack
