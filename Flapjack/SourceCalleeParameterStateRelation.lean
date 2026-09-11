import Flapjack.SourceCompiledFunctionLookup
import Flapjack.CompileCalleeParameterStateRelation

/-!
Source-function callee-entry adapter.

This is the compiler-facing boundary used by call correctness: source lookup
provides formal names and the body, `functionInfos` provides formal shapes,
and the generated callee parameter list provides the flattened Crep state
relation.
-/

namespace Flapjack

theorem panValueCrepStateRel_sourceFunctionParameters_of_lookup
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (values : List (PanValue α))
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody))
    (hinfo : lookupInfo name context.functions =
      some (parameters, returnShape))
    (hfunctions : context.functions = functionInfos declarations)
    (hvaluesLength : sourceParams.length = values.length)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : sourceParams.Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList parameters values 0,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList parameters values 0,
      parameter.slots.length = parameter.values.length) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      declaration.params = parameters ∧
      declaration.returnShape = returnShape ∧
      panValueCrepStateRel structs
        { context with vars := (compileParamVars declaration.params 0).1 }
        (foldCalleeParameterSource (fun _ => none)
          (compileCalleeParameterList declaration.params values 0))
        sourceGlobals sourceMemory
        { locals := foldCalleeParameterLocals (fun _ => none)
            (compileCalleeParameterList declaration.params values 0),
          memory := crepMemory } := by
  rw [hfunctions] at hinfo
  obtain ⟨declaration, hname, hsourceParams, hsourceBody,
      hdeclarationParams, hdeclarationReturn⟩ :=
    lookupInfo_functionInfos_of_source_lookup_eq declarations name sourceParams sourceBody
      parameters returnShape hlookup hinfo
  have hdeclLength : declaration.params.length = values.length := by
    have hnamesLength : declaration.params.length = sourceParams.length := by
      simpa using congrArg List.length hsourceParams
    exact hnamesLength.trans hvaluesLength
  have hdeclarationNames : (declaration.params.map Prod.fst).Nodup := by
    rw [hsourceParams]
    exact hnames
  cases hdeclarationParams
  refine ⟨declaration, hname, hsourceParams, hsourceBody, rfl, hdeclarationReturn, ?_⟩
  exact panValueCrepStateRel_compileFunDecl_context_of_folds
    structs context sourceGlobals sourceMemory crepMemory declaration values
    hdeclLength hglobals hmemory hcontext hdeclarationNames hshape hparameterLength

theorem panValueCrepStateRel_sourceFunctionParameters_of_source_lookup
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (values : List (PanValue α))
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody))
    (hfunctions : context.functions = functionInfos declarations)
    (hvaluesLength : sourceParams.length = values.length)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hcontext : context.vars = [])
    (hnames : sourceParams.Nodup)
    (hshape : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape),
      lookupInfo name (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape),
      lookupInfo name (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        parameter.slots.length = parameter.values.length) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      panValueCrepStateRel structs
        { context with vars := (compileParamVars declaration.params 0).1 }
        (foldCalleeParameterSource (fun _ => none)
          (compileCalleeParameterList declaration.params values 0))
        sourceGlobals sourceMemory
        { locals := foldCalleeParameterLocals (fun _ => none)
            (compileCalleeParameterList declaration.params values 0),
          memory := crepMemory } := by
  obtain ⟨found, hname, hparams, hbody, hinfo⟩ :=
    lookupInfo_functionInfos_of_source_lookup
      declarations name sourceParams sourceBody hlookup
  have hinfoContext : lookupInfo name context.functions =
      some (found.params, found.returnShape) := by
    rw [hfunctions]
    exact hinfo
  obtain ⟨declaration, hfoundName, hfoundParams, hfoundBody,
      hdeclarationParams, hdeclarationReturn, hstate⟩ :=
    panValueCrepStateRel_sourceFunctionParameters_of_lookup
      structs context declarations name sourceParams sourceBody
      found.params found.returnShape sourceGlobals sourceMemory crepMemory values
      hlookup hinfoContext hfunctions hvaluesLength hglobals hmemory hcontext hnames
      (hshape found.params found.returnShape hinfo)
      (hparameterLength found.params found.returnShape hinfo)
  exact ⟨declaration, hfoundName, hfoundParams, hfoundBody, hstate⟩

end Flapjack
