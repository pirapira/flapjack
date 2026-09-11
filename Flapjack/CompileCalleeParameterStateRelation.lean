import Flapjack.CompileCalleeParameterFreshness

/-!
Compiler-facing state relation for an evaluated callee parameter list.

The source call evaluator binds structured argument values by name, while the
Crep call evaluator receives the flattened words in the slots emitted by
`compileParamVars`.  This theorem assembles the existing freshness and bind /
assign transport into the context shape produced by the compiler.
-/

namespace Flapjack

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
      { context with vars := (compileParamVars params offset).1 }
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
  exact panValueCrepStateRel_parameters_append_of_context_bind_assign
    structs context
    { context with vars := (compileParamVars params offset).1 }
    sourceGlobals sourceMemory crepMemory
    (compileCalleeParameterList params values offset)
    calleeLocals targetCalleeLocals hglobals hmemory hbind hassign' hfresh hvars

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
      { context with vars := (compileParamVars params offset).1 }
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
  exact panValueCrepStateRel_parameters_append_of_context
    structs context
    { context with vars := (compileParamVars params offset).1 }
    sourceGlobals sourceMemory crepMemory
    (compileCalleeParameterList params values offset) hglobals hmemory hfresh hvars

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
            vars := (compileParamVars declaration.params 0).1
            maxVar := (compileParamVars declaration.params 0).2.2 }
        declaration.body := by
  simp [compileFunDecl]

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
      { context with vars := (compileParamVars declaration.params 0).1 }
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

end Flapjack
