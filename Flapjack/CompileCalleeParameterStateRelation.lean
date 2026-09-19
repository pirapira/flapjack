import Flapjack.CompileCalleeParameterFreshness

/-!
Compiler-facing state relation for an evaluated callee parameter list.

The source call evaluator binds structured argument values by name, while the
Crep call evaluator receives the flattened words in the slots emitted by
`compileParamVars`.  This theorem assembles the existing freshness and bind /
assign transport into the context shape produced by the compiler.
-/

namespace Flapjack

theorem lookupInfo_append
    [LawfulBEq String]
    (name : String) (left right : InfoMap α) :
    lookupInfo name (left ++ right) =
      match lookupInfo name left with
      | some value => some value
      | none => lookupInfo name right := by
  induction left with
  | nil => simp [lookupInfo]
  | cons entry left ih =>
      rcases entry with ⟨candidate, value⟩
      by_cases hcandidate : candidate == name
      · simp [lookupInfo, hcandidate]
      · simp [lookupInfo, hcandidate, ih]

theorem lookupInfo_reverse_of_nodup
    [LawfulBEq String]
    (name : String) (entries : InfoMap α)
    (hnames : entries.map Prod.fst |>.Nodup) :
    lookupInfo name entries.reverse = lookupInfo name entries := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      have hcons := List.nodup_cons.mp hnames
      have htail : (entries.map Prod.fst).Nodup := hcons.2
      have hcandidate : candidate ∉ entries.map Prod.fst := hcons.1
      by_cases hname : name = candidate
      · subst name
        have hnone : lookupInfo candidate entries.reverse = none := by
          apply lookupInfo_none_of_name_not_mem
          simpa using hcandidate
        simp [List.reverse_cons, lookupInfo_append, lookupInfo, hnone]
      · have hname' : candidate ≠ name := Ne.symm hname
        cases hlookup : lookupInfo name entries with
        | none =>
            simp [List.reverse_cons, lookupInfo_append, lookupInfo, hname',
              hlookup, ih htail]
        | some found =>
            simp [List.reverse_cons, lookupInfo_append, lookupInfo, hname',
              hlookup, ih htail]

theorem compileParamVars_names_nodup
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat)
    (hnames : (params.map Prod.fst).Nodup) :
    ((compileParamVars params offset).1.map Prod.fst).Nodup := by
  have hshapes := compileParamVars_preserves_parameter_shapes params offset
  have hnamesEq :
      (compileParamVars params offset).1.map Prod.fst = params.map Prod.fst := by
    simpa [Function.comp_def] using congrArg (List.map Prod.fst) hshapes
  rw [hnamesEq]
  exact hnames

theorem panValueCrepStateRel_reindex_vmap
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (params : List (VarName × Shape)) (offset : Nat)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α)
    (hnames : (params.map Prod.fst).Nodup)
    (hrel : panValueCrepStateRel structs
      { context with vars := (compileParamVars params offset).1 }
      sourceLocals sourceGlobals sourceMemory crepState) :
    panValueCrepStateRel structs
      { context with vars := (compileParamVars params offset).1.reverse }
      sourceLocals sourceGlobals sourceMemory crepState := by
  rcases hrel with ⟨hglobals, hlocals, hmemory⟩
  refine ⟨hglobals, ?_, hmemory⟩
  intro name value shape slots hsource hlookup
  apply hlocals name value shape slots hsource
  have hmapNames := compileParamVars_names_nodup params offset hnames
  change lookupInfo name (compileParamVars params offset).1.reverse =
    some (shape, slots) at hlookup
  rw [lookupInfo_reverse_of_nodup name (compileParamVars params offset).1 hmapNames] at hlookup
  exact hlookup

theorem panValueCrepStateRel_compileCalleeParameterList
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (calleeLocals : VarName → Option (PanValue α))
    (targetCalleeLocals : Nat → Option α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : (params.map Prod.fst).Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList params values offset,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList params values offset,
      parameter.slots.length = parameter.values.length)
    (hbind : bindPanValueParameters
        ((compileCalleeParameterList params values offset).map CalleeParameter.name)
        ((compileCalleeParameterList params values offset).map CalleeParameter.value) =
      some calleeLocals)
    (hassign : assignCrepValues (fun _ => none)
        (compileParamVars params offset).2.1
        (values.flatMap panValueFlatWords) = some targetCalleeLocals) :
    panValueCrepStateRel structs
      { context with vars := (compileParamVars params offset).1.reverse }
      calleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := crepMemory } := by
  have hfresh := compileCalleeParameterList_fresh_append
    structs context params values offset hlength hcontext hnames hshape
    hparameterLength
  have hassign' : assignCrepValues (fun _ => none)
      ((compileCalleeParameterList params values offset).flatMap CalleeParameter.slots)
      ((compileCalleeParameterList params values offset).flatMap CalleeParameter.values) =
      some targetCalleeLocals := by
    rw [compileCalleeParameterList_flattened_slots params values offset hlength,
      compileCalleeParameterList_flattened_values params values offset hlength]
    exact hassign
  have hvars :
      ({ context with vars := (compileParamVars params offset).1 } : CompileContext α).vars =
        (foldCalleeParameterContextAppend context
          (compileCalleeParameterList params values offset)).vars := by
    rw [foldCalleeParameterContextAppend_eq]
    simp [hcontext, compileCalleeParameterList_metadata params values offset hlength]
  have hrel := panValueCrepStateRel_parameters_append_of_context_bind_assign
    structs context
    { context with vars := (compileParamVars params offset).1 }
    sourceGlobals sourceMemory crepMemory
    (compileCalleeParameterList params values offset)
    calleeLocals targetCalleeLocals hglobals hmemory hbind hassign' hfresh hvars
  simpa [panToCrepMakeVmap] using
    (panValueCrepStateRel_reindex_vmap structs context params offset
    calleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := crepMemory } hnames hrel)

theorem panValueCrepStateRel_compileCalleeParameterList_of_folds
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : (params.map Prod.fst).Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList params values offset,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList params values offset,
      parameter.slots.length = parameter.values.length) :
    panValueCrepStateRel structs
      { context with vars := (compileParamVars params offset).1.reverse }
      (foldCalleeParameterSource (fun _ => none)
        (compileCalleeParameterList params values offset))
      sourceGlobals sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none)
          (compileCalleeParameterList params values offset),
        memory := crepMemory } := by
  have hfresh := compileCalleeParameterList_fresh_append
    structs context params values offset hlength hcontext hnames hshape
    hparameterLength
  have hvars :
      ({ context with vars := (compileParamVars params offset).1 } : CompileContext α).vars =
        (foldCalleeParameterContextAppend context
          (compileCalleeParameterList params values offset)).vars := by
    rw [foldCalleeParameterContextAppend_eq]
    simp [hcontext, compileCalleeParameterList_metadata params values offset hlength]
  have hrel := panValueCrepStateRel_parameters_append_of_context
    structs context
    { context with vars := (compileParamVars params offset).1 }
    sourceGlobals sourceMemory crepMemory
    (compileCalleeParameterList params values offset) hglobals hmemory hfresh hvars
  simpa [panToCrepMakeVmap] using
    (panValueCrepStateRel_reindex_vmap structs context params offset
    (foldCalleeParameterSource (fun _ => none)
      (compileCalleeParameterList params values offset)) sourceGlobals sourceMemory
    { locals := foldCalleeParameterLocals (fun _ => none)
        (compileCalleeParameterList params values offset),
      memory := crepMemory } hnames hrel)

theorem panValueCrepStateRel_compileCalleeParameterList_of_source_bind_assign
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (calleeLocals : VarName → Option (PanValue α))
    (targetCalleeLocals : Nat → Option α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : (params.map Prod.fst).Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList params values offset,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList params values offset,
      parameter.slots.length = parameter.values.length)
    (hbind : bindPanValueParameters (params.map Prod.fst) values = some calleeLocals)
    (hassign : assignCrepValues (fun _ => none)
        (compileParamVars params offset).2.1
        (values.flatMap panValueFlatWords) = some targetCalleeLocals) :
    panValueCrepStateRel structs
      { context with vars := (compileParamVars params offset).1.reverse }
      calleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := crepMemory } := by
  have hsource := bindPanValueParameters_compileCalleeParameterList_source
    params values offset hlength
  have hcallee : calleeLocals = foldCalleeParameterSource (fun _ => none)
      (compileCalleeParameterList params values offset) := by
    exact Option.some.inj (hbind.symm.trans hsource)
  have hgenerated := bindPanValueParameters_compileCalleeParameterList
    params values offset hlength
  have hbindGenerated : bindPanValueParameters
      ((compileCalleeParameterList params values offset).map CalleeParameter.name)
      ((compileCalleeParameterList params values offset).map CalleeParameter.value) =
      some calleeLocals := by
    simpa [hcallee] using hgenerated
  exact panValueCrepStateRel_compileCalleeParameterList structs context
    sourceGlobals sourceMemory crepMemory params values offset hlength calleeLocals
    targetCalleeLocals hglobals hmemory hcontext hnames hshape hparameterLength
    hbindGenerated hassign

theorem compileFunDecl_params_eq_compileParamVars
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α) :
    (compileFunDecl context declaration).params =
      (compileParamVars declaration.params 0).2.1 := by
  simp [compileFunDecl]

theorem compileFunDecl_body_eq_compileProg_parameter_context
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α) :
    (compileFunDecl context declaration).body =
      compileProg
        { context with
            vars := panToCrepMakeVmap declaration.params
            maxVar := (compileParamVars declaration.params 0).2.2 }
        declaration.body := by
  simp [compileFunDecl, panToCrepMakeVmap]

theorem panValueCrepStateRel_compileFunDecl_context_of_folds
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (declaration : FunDecl α) (values : List (PanValue α))
    (hlength : declaration.params.length = values.length)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : (declaration.params.map Prod.fst).Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList
        declaration.params values 0,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList
        declaration.params values 0,
      parameter.slots.length = parameter.values.length) :
    panValueCrepStateRel structs
      { context with vars := panToCrepMakeVmap declaration.params }
      (foldCalleeParameterSource (fun _ => none)
        (compileCalleeParameterList declaration.params values 0))
      sourceGlobals sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none)
          (compileCalleeParameterList declaration.params values 0),
        memory := crepMemory } := by
  exact panValueCrepStateRel_compileCalleeParameterList_of_folds
    structs context sourceGlobals sourceMemory crepMemory
    declaration.params values 0 hlength hglobals hmemory hcontext hnames hshape
    hparameterLength

theorem panValueCrepStateRel_reordered_parameter_context
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (params : List (VarName × Shape))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α)
    (hrel : panValueCrepStateRel structs
      { context with vars := (compileParamVars params 0).1 }
      sourceLocals sourceGlobals sourceMemory crepState)
    (hnames : (params.map Prod.fst).Nodup) :
    panValueCrepStateRel structs
      { context with vars := panToCrepMakeVmap params }
      sourceLocals sourceGlobals sourceMemory crepState := by
  have hnamesCompiled :
      ((compileParamVars params 0).1.map Prod.fst).Nodup := by
    have hnamesEq := congrArg (List.map Prod.fst)
      (compileParamVars_preserves_parameter_shapes params 0)
    have hnamesEq' :
        (compileParamVars params 0).1.map Prod.fst = params.map Prod.fst := by
      simpa [List.map_map, Function.comp_def] using hnamesEq
    rw [hnamesEq']
    exact hnames
  rcases hrel with ⟨hglobals, hlocals, hmemory⟩
  refine ⟨hglobals, ?_, hmemory⟩
  intro name value shape slots hsource hlookup
  have hlookupRaw : lookupInfo name (compileParamVars params 0).1 =
      some (shape, slots) := by
    rw [lookupInfo_reverse_of_nodup name
      (compileParamVars params 0).1 hnamesCompiled]
    simpa [panToCrepMakeVmap] using hlookup
  exact hlocals name value shape slots hsource hlookupRaw

end Flapjack
