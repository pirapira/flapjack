import Flapjack.CrepeCalleeParameterAppendRelation

/-!
Context equations for source-order callee parameters.

The parameter transport is defined with a fold so that its state-extension
proof follows the evaluator.  These equations expose the resulting context
record in the form produced by `compileFunDecl`, and allow its `maxVar` field
to differ without reproving the locals relation.
-/

namespace Flapjack

theorem foldCalleeParameterContextAppend_eq
    (context : CompileContext α) (parameters : List (CalleeParameter α)) :
    foldCalleeParameterContextAppend context parameters =
      { context with
          vars := context.vars ++ parameters.map
            (fun parameter =>
              (parameter.name, (parameter.shape, parameter.slots))) } := by
  induction parameters generalizing context with
  | nil => simp [foldCalleeParameterContextAppend]
  | cons parameter parameters ih =>
      change foldCalleeParameterContextAppend
        (addCalleeParameterContextAppend context parameter) parameters = _
      rw [ih]
      simp [addCalleeParameterContextAppend, List.append_assoc]

theorem foldCalleeParameterContextAppend_maxVar
    (context : CompileContext α) (parameters : List (CalleeParameter α)) :
    (foldCalleeParameterContextAppend context parameters).maxVar = context.maxVar := by
  induction parameters generalizing context with
  | nil => simp [foldCalleeParameterContextAppend]
  | cons parameter parameters ih =>
      change (foldCalleeParameterContextAppend
        (addCalleeParameterContextAppend context parameter) parameters).maxVar = _
      rw [ih]
      rfl

theorem panValueCrepStateRel_parameters_append_of_context
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context targetContext : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hfresh : CalleeParameterListFreshAppend structs context parameters)
    (hvars : targetContext.vars =
      (foldCalleeParameterContextAppend context parameters).vars) :
    panValueCrepStateRel structs targetContext
      (foldCalleeParameterSource (fun _ => none) parameters) sourceGlobals
      sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none) parameters,
        memory := crepMemory } := by
  have hrel := panValueCrepCalleeStateRel_parameters_append structs context
    sourceGlobals sourceMemory crepMemory parameters hglobals hmemory hfresh
  simpa [panValueCrepStateRel, panValueCrepLocalsRel, hvars] using hrel

theorem panValueCrepStateRel_parameters_append_of_context_bind_assign
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context targetContext : CompileContext α)
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
    (hfresh : CalleeParameterListFreshAppend structs context parameters)
    (hvars : targetContext.vars =
      (foldCalleeParameterContextAppend context parameters).vars) :
    panValueCrepStateRel structs targetContext calleeLocals sourceGlobals
      sourceMemory { locals := targetCalleeLocals, memory := crepMemory } := by
  have hrel := panValueCrepCalleeStateRel_parameters_append_of_bind_assign
    structs context sourceGlobals sourceMemory crepMemory parameters calleeLocals
    targetCalleeLocals hglobals hmemory hbind hassign hfresh
  simpa [panValueCrepStateRel, panValueCrepLocalsRel, hvars] using hrel

end Flapjack
