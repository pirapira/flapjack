import Flapjack.SourceCompiledFunctionCalleeContext
import Flapjack.SourceCalleeParameterStateRelation

/-!
Combined source/compiled callee-entry packaging.

This is the lookup boundary consumed by call correctness: one declaration
witness identifies the source callee, its `compileFunDecl` entry, and the
parameter-state relation for the generated callee context.
-/

namespace Flapjack

theorem sourceFunctionCalleeEntry_compileToCrepe_of_lookup
    [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (values : List (PanValue α))
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody))
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
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) ∧
      lookupCompiledFunction name (compileToCrepe context declarations) =
        some ((compileFunDecl
          { context with functions := functionInfos declarations } declaration).params,
          (compileFunDecl
            { context with functions := functionInfos declarations } declaration).body) ∧
      panValueCrepStateRel structs
        { context with
            functions := functionInfos declarations
            vars := (compileParamVars declaration.params 0).1 }
        (foldCalleeParameterSource (fun _ => none)
          (compileCalleeParameterList declaration.params values 0))
        sourceGlobals sourceMemory
        { locals := foldCalleeParameterLocals (fun _ => none)
            (compileCalleeParameterList declaration.params values 0),
          memory := crepMemory } := by
  obtain ⟨found, _, hfoundParams, _, hinfo⟩ :=
    lookupInfo_functionInfos_of_source_lookup
      declarations name sourceParams sourceBody hlookup
  obtain ⟨declaration, hdeclarationName, hdeclarationParamsSource,
      hdeclarationBody, hdeclarationParams, hdeclarationReturnShape,
      hcompiled⟩ :=
    lookupCompiledFunction_compileToCrepe_of_source_lookup_and_info
      context declarations name sourceParams sourceBody
      found.params found.returnShape hlookup hinfo
  have hdeclarationInfo : lookupInfo name (functionInfos declarations) =
      some (declaration.params, declaration.returnShape) := by
    rw [hdeclarationParams, hdeclarationReturnShape]
    exact hinfo
  have hlength : declaration.params.length = values.length := by
    calc
      declaration.params.length = found.params.length := by
        rw [hdeclarationParams]
      _ = (found.params.map Prod.fst).length := by simp
      _ = sourceParams.length := congrArg List.length hfoundParams
      _ = values.length := hvaluesLength
  have hnamesDeclaration : (declaration.params.map Prod.fst).Nodup := by
    rw [hdeclarationParams, hfoundParams]
    exact hnames
  have hstate := panValueCrepStateRel_compileFunDecl_context_of_folds
    structs { context with functions := functionInfos declarations }
    sourceGlobals sourceMemory crepMemory declaration values hlength hglobals hmemory
    hcontext hnamesDeclaration
    (hshape declaration.params declaration.returnShape hdeclarationInfo)
    (hparameterLength declaration.params declaration.returnShape hdeclarationInfo)
  refine ⟨declaration, hdeclarationName, hdeclarationParamsSource,
    hdeclarationBody, hdeclarationInfo, hcompiled, ?_⟩
  exact hstate

end Flapjack
