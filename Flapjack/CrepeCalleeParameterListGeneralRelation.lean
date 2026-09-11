import Flapjack.CrepeCalleeParameterRelation

/-!
List-level callee-entry transport for arbitrary structured parameters.

Each entry records the source shape, the compiler-assigned Crep slots, the
source value, and its flattened words.  The source and target evaluator
equations are exposed alongside the state relation so call inversion can use
the theorem directly.
-/

namespace Flapjack

structure CalleeParameter (α : Type u) where
  name : VarName
  shape : Shape
  slots : List Nat
  value : PanValue α
  values : List α

def addCalleeParameterContext (context : CompileContext α)
    (parameter : CalleeParameter α) : CompileContext α :=
  { context with vars := (parameter.name, (parameter.shape, parameter.slots)) :: context.vars }

def foldCalleeParameterContext (context : CompileContext α)
    (parameters : List (CalleeParameter α)) : CompileContext α :=
  parameters.foldl addCalleeParameterContext context

def foldCalleeParameterSource [BEq VarName]
    (locals : VarName → Option (PanValue α))
    (parameters : List (CalleeParameter α)) : VarName → Option (PanValue α) :=
  parameters.foldl
    (fun locals parameter => updatePanValueMap locals parameter.name parameter.value)
    locals

def foldCalleeParameterLocals
    (locals : Nat → Option α)
    (parameters : List (CalleeParameter α)) : Nat → Option α :=
  parameters.foldl
    (fun locals parameter =>
      updateCrepLocalList locals parameter.slots parameter.values)
    locals

def CalleeParameterListFresh [BEq String]
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
      CalleeParameterListFresh structs
        (addCalleeParameterContext context parameter) parameters

theorem calleeParameterListFresh_length
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (parameters : List (CalleeParameter α))
    (hfresh : CalleeParameterListFresh structs context parameters) :
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
      · exact ih (context := addCalleeParameterContext context parameter)
          htail current hcurrent

theorem panValueCrepStateRel_add_parameters_fresh
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (parameters : List (CalleeParameter α))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hfresh : CalleeParameterListFresh structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContext context parameters)
      (foldCalleeParameterSource sourceLocals parameters) sourceGlobals
      sourceMemory
      { state with locals := foldCalleeParameterLocals state.locals parameters } := by
  induction parameters generalizing context sourceLocals state with
  | nil =>
      simpa [foldCalleeParameterContext, foldCalleeParameterSource,
        foldCalleeParameterLocals] using hrel
  | cons parameter parameters ih =>
      rcases hfresh with ⟨hname, hshape, hlength, hdistinct, hflat, hnoalias, htail⟩
      have hstep := panValueCrepStateRel_add_parameter_fresh
        structs context sourceLocals sourceGlobals sourceMemory state
        parameter.name parameter.shape parameter.slots parameter.value
        parameter.values hrel hname hshape hlength hdistinct hflat hnoalias
      have hrest := ih
        (context := addCalleeParameterContext context parameter)
        (sourceLocals := updatePanValueMap sourceLocals parameter.name parameter.value)
        (state := { state with
          locals := updateCrepLocalList state.locals parameter.slots parameter.values })
        hstep htail
      simpa [foldCalleeParameterContext, foldCalleeParameterSource,
        foldCalleeParameterLocals, addCalleeParameterContext] using hrest

theorem foldCalleeParameterSource_map
    (parameters : List (CalleeParameter α))
    (locals : VarName → Option (PanValue α)) :
    (parameters.map (fun parameter => (parameter.name, parameter.value))).foldl
        (fun locals (name, value) => updatePanValueMap locals name value) locals =
      foldCalleeParameterSource locals parameters := by
  induction parameters generalizing locals with
  | nil => rfl
  | cons parameter parameters ih =>
      simp [foldCalleeParameterSource, ih]

theorem bindPanValueParameters_parameters
    (parameters : List (CalleeParameter α)) :
    bindPanValueParameters (parameters.map CalleeParameter.name)
        (parameters.map CalleeParameter.value) =
      some (foldCalleeParameterSource (fun _ => none) parameters) := by
  have hzip :
      (parameters.map CalleeParameter.name).zip
          (parameters.map CalleeParameter.value) =
        parameters.map (fun parameter => (parameter.name, parameter.value)) := by
    induction parameters with
    | nil => rfl
    | cons parameter parameters ih =>
        simp [ih]
  simp [bindPanValueParameters, foldCalleeParameterSource, hzip,
    foldCalleeParameterSource_map]

theorem foldZipUpdateCrepLocalList
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (hlength : names.length = values.length) :
    (names.zip values).foldl
        (fun locals (name, value) => updateCrepLocal locals name value) locals =
      updateCrepLocalList locals names values := by
  induction names generalizing locals values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at hlength
  | cons name names ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp at hlength
            exact hlength
          simp only [List.zip_cons_cons, List.foldl]
          rw [ih (locals := updateCrepLocal locals name value)
            (values := values) hlengthTail]
          rfl

theorem flatMapCalleeParameterLengths
    (parameters : List (CalleeParameter α))
    (hlength : ∀ parameter ∈ parameters,
      parameter.slots.length = parameter.values.length) :
    (parameters.flatMap CalleeParameter.slots).length =
      (parameters.flatMap CalleeParameter.values).length := by
  induction parameters with
  | nil => rfl
  | cons parameter parameters ih =>
      have hhead := hlength parameter (by simp)
      have htail : ∀ parameter ∈ parameters,
          parameter.slots.length = parameter.values.length := by
        intro current hcurrent
        exact hlength current (by simp [hcurrent])
      change (parameter.slots ++ parameters.flatMap CalleeParameter.slots).length =
        (parameter.values ++ parameters.flatMap CalleeParameter.values).length
      simp only [List.length_append]
      rw [hhead, ih htail]

theorem updateCrepLocalList_append
    (locals : Nat → Option α) (names names' : List Nat)
    (values values' : List α) (hlength : names.length = values.length) :
    updateCrepLocalList locals (names ++ names') (values ++ values') =
      updateCrepLocalList (updateCrepLocalList locals names values)
        names' values' := by
  induction names generalizing locals values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at hlength
  | cons name names ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp at hlength
            exact hlength
          simpa [updateCrepLocalList] using
            ih (locals := updateCrepLocal locals name value)
              (values := values) hlengthTail

theorem foldCalleeParameterLocals_flatMap
    (locals : Nat → Option α) (parameters : List (CalleeParameter α))
    (hlength : ∀ parameter ∈ parameters,
      parameter.slots.length = parameter.values.length) :
    foldCalleeParameterLocals locals parameters =
      updateCrepLocalList locals (parameters.flatMap CalleeParameter.slots)
        (parameters.flatMap CalleeParameter.values) := by
  induction parameters generalizing locals with
  | nil => rfl
  | cons parameter parameters ih =>
      have hhead := hlength parameter (by simp)
      have htail : ∀ parameter ∈ parameters,
          parameter.slots.length = parameter.values.length := by
        intro current hcurrent
        exact hlength current (by simp [hcurrent])
      change foldCalleeParameterLocals
          (updateCrepLocalList locals parameter.slots parameter.values) parameters =
        updateCrepLocalList locals
          (parameter.slots ++ parameters.flatMap CalleeParameter.slots)
          (parameter.values ++ parameters.flatMap CalleeParameter.values)
      rw [ih (locals := updateCrepLocalList locals parameter.slots parameter.values)
        htail]
      exact (updateCrepLocalList_append locals parameter.slots
        (parameters.flatMap CalleeParameter.slots) parameter.values
        (parameters.flatMap CalleeParameter.values) hhead).symm

theorem assignCrepValues_parameters
    (parameters : List (CalleeParameter α))
    (hlength : ∀ parameter ∈ parameters,
      parameter.slots.length = parameter.values.length) :
    assignCrepValues (fun _ => none)
        (parameters.flatMap CalleeParameter.slots)
        (parameters.flatMap CalleeParameter.values) =
      some (foldCalleeParameterLocals (fun _ => none) parameters) := by
  induction parameters with
  | nil => simp [assignCrepValues, foldCalleeParameterLocals]
  | cons parameter parameters ih =>
      have htail : ∀ parameter ∈ parameters,
          parameter.slots.length = parameter.values.length := by
        intro current hcurrent
        exact hlength current (by simp [hcurrent])
      have hhead := hlength parameter (by simp)
      have htailLength :
          (parameters.flatMap CalleeParameter.slots).length =
            (parameters.flatMap CalleeParameter.values).length := by
        exact flatMapCalleeParameterLengths parameters htail
      have htotalLength :
          (parameter.slots ++ parameters.flatMap CalleeParameter.slots).length =
            (parameter.values ++ parameters.flatMap CalleeParameter.values).length := by
        simp only [List.length_append]
        rw [hhead, htailLength]
      have hzip :
          (parameter.slots ++ parameters.flatMap CalleeParameter.slots).zip
              (parameter.values ++ parameters.flatMap CalleeParameter.values) =
            parameter.slots.zip parameter.values ++
              (parameters.flatMap CalleeParameter.slots).zip
                (parameters.flatMap CalleeParameter.values) := by
        simp [List.zip_append, hhead]
      change assignCrepValues (fun _ => none)
        (parameter.slots ++ parameters.flatMap CalleeParameter.slots)
        (parameter.values ++ parameters.flatMap CalleeParameter.values) =
          some (foldCalleeParameterLocals (fun _ => none) (parameter :: parameters))
      simp only [assignCrepValues]
      rw [htotalLength]
      simp
      rw [hzip, List.foldl_append,
        foldZipUpdateCrepLocalList _ _ _ hhead,
        foldZipUpdateCrepLocalList _ _ _ htailLength]
      change updateCrepLocalList (updateCrepLocalList (fun _ => none)
          parameter.slots parameter.values)
          (parameters.flatMap CalleeParameter.slots)
          (parameters.flatMap CalleeParameter.values) =
        foldCalleeParameterLocals
          (updateCrepLocalList (fun _ => none) parameter.slots parameter.values)
          parameters
      exact (foldCalleeParameterLocals_flatMap
        (updateCrepLocalList (fun _ => none) parameter.slots parameter.values)
        parameters htail).symm

theorem panValueCrepCalleeStateRel_parameters
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hfresh : CalleeParameterListFresh structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContext context parameters)
      (foldCalleeParameterSource (fun _ => none) parameters) sourceGlobals
      sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none) parameters,
        memory := crepMemory } := by
  have hrel : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { locals := (fun _ => none), memory := crepMemory } := by
    refine ⟨hglobals, panValueCrepLocalsRel_empty structs context (fun _ => none), ?_⟩
    exact hmemory
  exact panValueCrepStateRel_add_parameters_fresh structs context
    (fun _ => none) sourceGlobals sourceMemory
    { locals := (fun _ => none), memory := crepMemory }
    parameters hrel hfresh

theorem panValueCrepCalleeStateRel_parameters_of_bind_assign
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
    (hfresh : CalleeParameterListFresh structs context parameters) :
    panValueCrepStateRel structs
      (foldCalleeParameterContext context parameters) calleeLocals sourceGlobals
      sourceMemory
      { locals := targetCalleeLocals, memory := crepMemory } := by
  have hbound := bindPanValueParameters_parameters parameters
  have hcallee : calleeLocals = foldCalleeParameterSource
      (fun _ => none) parameters := by
    exact Option.some.inj (hbind.symm.trans hbound)
  have hlength := calleeParameterListFresh_length structs context parameters hfresh
  have hassigned := assignCrepValues_parameters parameters hlength
  have htarget : targetCalleeLocals = foldCalleeParameterLocals
      (fun _ => none) parameters := by
    exact Option.some.inj (hassign.symm.trans hassigned)
  have hrel := panValueCrepCalleeStateRel_parameters structs context
    sourceGlobals sourceMemory crepMemory parameters hglobals hmemory hfresh
  simpa [hcallee, htarget] using hrel

end Flapjack
