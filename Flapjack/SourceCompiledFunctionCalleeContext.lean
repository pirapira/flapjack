import Flapjack.SourceCompiledFunctionLookup
import Flapjack.CompileCalleeParameterStateRelation

/-!
Compiled function lookup in compiler-native form.

The source/compiled lookup theorem exposes the generated parameter slots and
body as expanded `compileParamVars` expressions.  The call correctness proof
needs the same entry as `compileFunDecl`, so that its parameter-state relation
and body-context equation can be used without another ad-hoc unfolding.
-/

namespace Flapjack

theorem lookupCompiledFunction_compileToCrepe_of_source_lookup_eq_compileFunDecl
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupCompiledFunction name (compileToCrepe context declarations) =
        some ((compileFunDecl
          { context with functions := functionInfos declarations } declaration).params,
          (compileFunDecl
            { context with functions := functionInfos declarations } declaration).body) := by
  obtain ⟨declaration, hname, hparams, hbody, hcompiled⟩ :=
    lookupCompiledFunction_compileToCrepe_of_source_lookup
      context declarations name sourceParams sourceBody hlookup
  refine ⟨declaration, hname, hparams, hbody, ?_⟩
  simpa [compileFunDecl] using hcompiled

theorem lookupCompiledFunction_compileFunctions_of_source_lookup_and_info
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody))
    (hinfo : lookupInfo name (functionInfos declarations) =
      some (parameters, returnShape)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      declaration.params = parameters ∧
      declaration.returnShape = returnShape ∧
      lookupCompiledFunction name (compileFunctions context declarations) =
        some ((compileFunDecl context declaration).params,
          (compileFunDecl context declaration).body) := by
  induction declarations with
  | nil =>
      simp [sourceFunctionEntries, lookupPanFunction] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name = declaration.name
          · have hsourcePair :
                (declaration.params.map Prod.fst, declaration.body) =
                  (sourceParams, sourceBody) := by
                exact Option.some.inj (by
                  simpa [sourceFunctionEntries, lookupPanFunction, hname] using hlookup)
            have hinfoPair :
                (declaration.params, declaration.returnShape) =
                  (parameters, returnShape) := by
                exact Option.some.inj (by
                  simpa [functionInfos, lookupInfo, hname] using hinfo)
            cases hsourcePair
            cases hinfoPair
            refine ⟨declaration, hname.symm, rfl, rfl, rfl, rfl, ?_⟩
            simpa [compileFunDecl, hname] using
              (lookupCompiledFunction_compileFunctions_head
                context declaration declarations)
          · have hname' : declaration.name ≠ name := by
              intro heq
              exact hname heq.symm
            have hsourceTail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (sourceParams, sourceBody) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname, hname'] using hlookup
            have hinfoTail :
                lookupInfo name (functionInfos declarations) =
                  some (parameters, returnShape) := by
                simpa [functionInfos, lookupInfo, hname, hname'] using hinfo
            obtain ⟨found, hfoundName, hfoundParams, hfoundBody,
                hfoundDeclarationParams, hfoundReturnShape, hfoundLookup⟩ :=
              ih hsourceTail hinfoTail
            refine ⟨found, hfoundName, hfoundParams, hfoundBody,
              hfoundDeclarationParams, hfoundReturnShape, ?_⟩
            exact lookupCompiledFunction_compileFunctions_skip_nonmatching
              context declaration declarations name
              (compileFunDecl context found).params
              (compileFunDecl context found).body hname hfoundLookup
      | decl shape declaration value =>
          have hsourceTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          have hinfoTail :
              lookupInfo name (functionInfos declarations) =
                some (parameters, returnShape) := by
            simpa [functionInfos] using hinfo
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody,
              hfoundDeclarationParams, hfoundReturnShape, hfoundLookup⟩ :=
            ih hsourceTail hinfoTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody,
            hfoundDeclarationParams, hfoundReturnShape, ?_⟩
          simpa [compileFunctions] using hfoundLookup
      | exnDecl exception shape =>
          have hsourceTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          have hinfoTail :
              lookupInfo name (functionInfos declarations) =
                some (parameters, returnShape) := by
            simpa [functionInfos] using hinfo
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody,
              hfoundDeclarationParams, hfoundReturnShape, hfoundLookup⟩ :=
            ih hsourceTail hinfoTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody,
            hfoundDeclarationParams, hfoundReturnShape, ?_⟩
          simpa [compileFunctions] using hfoundLookup
      | name struct fields =>
          have hsourceTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          have hinfoTail :
              lookupInfo name (functionInfos declarations) =
                some (parameters, returnShape) := by
            simpa [functionInfos] using hinfo
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody,
              hfoundDeclarationParams, hfoundReturnShape, hfoundLookup⟩ :=
            ih hsourceTail hinfoTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody,
            hfoundDeclarationParams, hfoundReturnShape, ?_⟩
          simpa [compileFunctions] using hfoundLookup

theorem lookupCompiledFunction_compileToCrepe_of_source_lookup_and_info
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody))
    (hinfo : lookupInfo name (functionInfos declarations) =
      some (parameters, returnShape)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      declaration.params = parameters ∧
      declaration.returnShape = returnShape ∧
      lookupCompiledFunction name (compileToCrepe context declarations) =
        some ((compileFunDecl
          { context with functions := functionInfos declarations } declaration).params,
          (compileFunDecl
            { context with functions := functionInfos declarations } declaration).body) := by
  obtain ⟨declaration, hname, hparams, hbody, hdeclarationParams,
      hdeclarationReturnShape, hcompiled⟩ :=
    lookupCompiledFunction_compileFunctions_of_source_lookup_and_info
      { context with functions := functionInfos declarations } declarations
      name sourceParams sourceBody parameters returnShape hlookup hinfo
  refine ⟨declaration, hname, hparams, hbody, hdeclarationParams,
    hdeclarationReturnShape, ?_⟩
  simpa [compileToCrepe] using hcompiled

end Flapjack
