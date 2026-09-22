import Flapjack.CompileCalleeParameterFreshness
import Flapjack.PanToCrepCorrectnessBoundary

/-!
Compiler-facing state relation for an evaluated callee parameter list.

The source call evaluator binds structured argument values by name, while the
Crep call evaluator receives the flattened words in the slots emitted by
`compileParamVars`.  This theorem assembles the existing freshness and bind /
assign transport into the context shape produced by the compiler.
-/

namespace Flapjack

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
  have hlookupRaw : lookupInfo name (compileParamVars params offset).1 =
      some (shape, slots) := by
    rw [lookupInfo_reverse_of_nodup name
      (compileParamVars params offset).1 hmapNames]
    exact hlookup
  exact hlookupRaw

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

theorem compileFunDecl_parameter_context_slots_bounded
    [LawfulBEq String]
    (context : CompileContext α) (declaration : FunDecl α)
    (hnames : (declaration.params.map Prod.fst).Nodup) :
    ∀ name shape names,
      lookupInfo name
          ({ context with
              vars := panToCrepMakeVmap declaration.params
              maxVar := (compileParamVars declaration.params 0).2.2 } :
            CompileContext α).vars = some (shape, names) →
      ∀ slot ∈ names,
        slot ≤ ({ context with
          vars := panToCrepMakeVmap declaration.params
          maxVar := (compileParamVars declaration.params 0).2.2 } :
        CompileContext α).maxVar := by
  intro name shape names hlookup slot hslot
  have hnamesCompiled := compileParamVars_names_nodup
    declaration.params 0 hnames
  have hlookupRaw : lookupInfo name
      (compileParamVars declaration.params 0).1 = some (shape, names) := by
    change lookupInfo name (compileParamVars declaration.params 0).1.reverse =
      some (shape, names) at hlookup
    rw [← lookupInfo_reverse_of_nodup name
      (compileParamVars declaration.params 0).1 hnamesCompiled] at hlookup
    exact hlookup
  change slot ≤ (compileParamVars declaration.params 0).2.2
  exact compileParamVars_slot_le declaration.params 0 name shape names
    hlookupRaw slot hslot

/-! The source-shaped compiler follows Cake's `comp_func` convention: its
    parameter context stores `shapeSize - 1` as `maxVar`, rather than the next
    free slot used by `compileFunDecl`.  This is the corresponding bounded-slot
    fact for `panToCrepCompFunc`/`compileFunDeclSource`. -/
theorem compileFunDeclSource_parameter_context_slots_bounded
    [LawfulBEq String]
    (context : CompileContext α) (declaration : FunDecl α)
    (hnames : (declaration.params.map Prod.fst).Nodup) :
    ∀ name shape names,
      lookupInfo name
          ({ context with
              vars := panToCrepMakeVmap declaration.params
              maxVar := Shape.shapeSize
                (.comb (declaration.params.map Prod.snd)) - 1 } :
            CompileContext α).vars = some (shape, names) →
      ∀ slot ∈ names,
        slot ≤ ({ context with
          vars := panToCrepMakeVmap declaration.params
          maxVar := Shape.shapeSize
            (.comb (declaration.params.map Prod.snd)) - 1 } :
        CompileContext α).maxVar := by
  intro name shape names hlookup slot hslot
  have hnamesCompiled := compileParamVars_names_nodup
    declaration.params 0 hnames
  have hlookupRaw : lookupInfo name
      (compileParamVars declaration.params 0).1 = some (shape, names) := by
    change lookupInfo name (compileParamVars declaration.params 0).1.reverse =
      some (shape, names) at hlookup
    rw [← lookupInfo_reverse_of_nodup name
      (compileParamVars declaration.params 0).1 hnamesCompiled] at hlookup
    exact hlookup
  have hlt := compileParamVars_slot_lt declaration.params 0 name shape names
    hlookupRaw slot hslot
  have hnext := compileParamVars_next_offset declaration.params 0
  change slot ≤ Shape.shapeSize
    (.comb (declaration.params.map Prod.snd)) - 1
  omega

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

/-! Package the fold-based callee relation with Cake's declaration-entry
    `no_overlap` and `ctxt_max` invariants.  This is the declaration-state
    witness consumed by the `state_rel_imp_semantics_decls_to_crep` call step;
    the evaluator and call-result premises remain at the caller boundary. -/
theorem panValueCrepStateRel_compileFunDecl_context_with_invariants_of_folds
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
    panValueCrepStateRelWithContext structs
      { context with
          vars := panToCrepMakeVmap declaration.params
          maxVar := (compileParamVars declaration.params 0).2.2 - 1 }
      (foldCalleeParameterSource (fun _ => none)
        (compileCalleeParameterList declaration.params values 0))
      sourceGlobals sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none)
          (compileCalleeParameterList declaration.params values 0),
        memory := crepMemory } := by
  have hstate := panValueCrepStateRel_compileFunDecl_context_of_folds
    structs context sourceGlobals sourceMemory crepMemory declaration values
    hlength hglobals hmemory hcontext hnames hshape hparameterLength
  have hinvariants := panToCrepMakeVmap_context_invariants
    declaration.params hnames
  have hstate' : panValueCrepStateRel structs
      { context with
          vars := panToCrepMakeVmap declaration.params
          maxVar := (compileParamVars declaration.params 0).2.2 - 1 }
      (foldCalleeParameterSource (fun _ => none)
        (compileCalleeParameterList declaration.params values 0))
      sourceGlobals sourceMemory
      { locals := foldCalleeParameterLocals (fun _ => none)
          (compileCalleeParameterList declaration.params values 0),
        memory := crepMemory } := by
    rcases hstate with ⟨hglobals', hlocals, hmemory'⟩
    refine ⟨hglobals', ?_, hmemory'⟩
    intro name value shape slots hsource hlookup
    exact hlocals name value shape slots hsource hlookup
  exact ⟨hinvariants.1, hinvariants.2, hstate'⟩

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
    have hlookup' := hlookup
    change lookupInfo name (compileParamVars params 0).1.reverse =
      some (shape, slots) at hlookup'
    rw [lookupInfo_reverse_of_nodup name
      (compileParamVars params 0).1 hnamesCompiled]
    exact hlookup'
  exact hlocals name value shape slots hsource hlookupRaw

end Flapjack
