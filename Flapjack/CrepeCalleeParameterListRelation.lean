import Flapjack.CrepeCalleeParameterWordRelation

/-!
List-level callee parameter transport for word-valued parameters.

The source and Crep evaluators both bind parameters with left folds.  This
file exposes the corresponding state relation as a fold theorem, using the
one-parameter fresh-slot theorem at each step.
-/

namespace Flapjack

abbrev WordParameter (α : Type u) := VarName × Nat × α

def addWordParameterContext (context : CompileContext α)
    (parameter : WordParameter α) : CompileContext α :=
  match parameter with
  | (name, slot, _) =>
      { context with vars := (name, (.one, [slot])) :: context.vars }

def foldWordParameterContext (context : CompileContext α)
    (parameters : List (WordParameter α)) : CompileContext α :=
  parameters.foldl addWordParameterContext context

def foldWordParameterSource [BEq VarName]
    (locals : VarName → Option (PanValue α))
    (parameters : List (WordParameter α)) : VarName → Option (PanValue α) :=
  parameters.foldl
    (fun locals (name, _, value) => updatePanValueMap locals name (.word value))
    locals

def foldWordParameterLocals
    (locals : Nat → Option α)
    (parameters : List (WordParameter α)) : Nat → Option α :=
  parameters.foldl
    (fun locals (_, slot, value) => updateCrepLocal locals slot value)
    locals

def WordParameterListFresh [BEq String]
    (context : CompileContext α) : List (WordParameter α) → Prop
  | [] => True
  | (name, slot, value) :: parameters =>
      lookupInfo name context.vars = none ∧
      (∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        slot ∉ oldSlots) ∧
      WordParameterListFresh
        (addWordParameterContext context (name, slot, value)) parameters

theorem foldWordParameterSource_map
    (parameters : List (WordParameter α))
    (locals : VarName → Option (PanValue α)) :
    (parameters.map (fun (name, _, value) =>
      (name, PanValue.word value))).foldl
        (fun locals (name, value) => updatePanValueMap locals name value) locals =
      foldWordParameterSource locals parameters := by
  induction parameters generalizing locals with
  | nil => rfl
  | cons parameter parameters ih =>
      rcases parameter with ⟨name, slot, value⟩
      simp [foldWordParameterSource, ih]

theorem foldWordParameterLocals_map
    (parameters : List (WordParameter α))
    (locals : Nat → Option α) :
    (parameters.map (fun (_, slot, value) => (slot, value))).foldl
        (fun locals (slot, value) => updateCrepLocal locals slot value) locals =
      foldWordParameterLocals locals parameters := by
  induction parameters generalizing locals with
  | nil => rfl
  | cons parameter parameters ih =>
      rcases parameter with ⟨name, slot, value⟩
      simp [foldWordParameterLocals, ih]

theorem panValueCrepStateRel_add_word_parameters_fresh
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (parameters : List (WordParameter α))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hfresh : WordParameterListFresh context parameters) :
    panValueCrepStateRel structs
      (foldWordParameterContext context parameters)
      (foldWordParameterSource sourceLocals parameters) sourceGlobals
      sourceMemory
      { state with locals := foldWordParameterLocals state.locals parameters } := by
  induction parameters generalizing context sourceLocals state with
  | nil =>
      simpa [foldWordParameterContext, foldWordParameterSource,
        foldWordParameterLocals] using hrel
  | cons parameter parameters ih =>
      rcases parameter with ⟨name, slot, value⟩
      rcases hfresh with ⟨hname, hslot, htail⟩
      have hstep := panValueCrepStateRel_add_word_parameter_fresh
        structs context sourceLocals sourceGlobals sourceMemory state
        name slot value hrel hname hslot
      have hrest := ih
        (context := addWordParameterContext context (name, slot, value))
        (sourceLocals := updatePanValueMap sourceLocals name (.word value))
        (state := { state with locals := updateCrepLocal state.locals slot value })
        hstep htail
      simpa [foldWordParameterContext, foldWordParameterSource,
        foldWordParameterLocals, addWordParameterContext] using hrest

theorem bindPanValueParameters_word_parameters
    (parameters : List (WordParameter α)) :
    bindPanValueParameters
        (parameters.map (fun (name, _, _) => name))
      (parameters.map (fun (_, _, value) => PanValue.word value)) =
      some (foldWordParameterSource (fun _ => none) parameters) := by
  have hzip :
      (parameters.map (fun (name, _, _) => name)).zip
          (parameters.map (fun (_, _, value) => PanValue.word value)) =
        parameters.map (fun (name, _, value) =>
          (name, PanValue.word value)) := by
    induction parameters with
    | nil => rfl
    | cons parameter parameters ih =>
        rcases parameter with ⟨name, slot, value⟩
        simp [ih]
  simp [bindPanValueParameters, foldWordParameterSource, hzip,
    foldWordParameterSource_map]

theorem assignCrepValues_word_parameters
    (parameters : List (WordParameter α)) :
    assignCrepValues (fun _ => none)
        (parameters.map (fun (_, slot, _) => slot))
      (parameters.map (fun (_, _, value) => value)) =
      some (foldWordParameterLocals (fun _ => none) parameters) := by
  have hzip :
      (parameters.map (fun (_, slot, _) => slot)).zip
          (parameters.map (fun (_, _, value) => value)) =
        parameters.map (fun (_, slot, value) => (slot, value)) := by
    induction parameters with
    | nil => rfl
    | cons parameter parameters ih =>
        rcases parameter with ⟨name, slot, value⟩
        simp [ih]
  simp [assignCrepValues, foldWordParameterLocals, hzip,
    foldWordParameterLocals_map]

theorem panValueCrepCalleeStateRel_word_parameters
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (WordParameter α))
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hfresh : WordParameterListFresh context parameters) :
    panValueCrepStateRel structs
      (foldWordParameterContext context parameters)
      (foldWordParameterSource (fun _ => none) parameters) sourceGlobals
      sourceMemory
      { locals := foldWordParameterLocals (fun _ => none) parameters,
        memory := crepMemory } := by
  have hrel : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { locals := (fun _ => none), memory := crepMemory } := by
    refine ⟨hglobals, panValueCrepLocalsRel_empty structs context (fun _ => none), ?_⟩
    exact hmemory
  exact panValueCrepStateRel_add_word_parameters_fresh structs context
    (fun _ => none) sourceGlobals sourceMemory
    { locals := (fun _ => none), memory := crepMemory }
    parameters hrel hfresh

end Flapjack
