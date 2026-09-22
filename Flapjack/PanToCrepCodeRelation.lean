import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.SourceCompiledFunctionLookup

/-!
Concrete code-table correspondence for the source-shaped Pancake compiler.

This is the Lean counterpart of Cake's `mk_ctxt_code_imp_code_rel` in
`pan_to_crepProofScript.sml`.  The source table is the function projection of
the declaration list and the target table is the public `compileToCrep`
result.  The proof deliberately goes through the source/compiled lookup
lemmas instead of weakening `panValuePcCodeRelConcrete` or postulating a
relation at the top-level correctness theorem.
-/

namespace Flapjack

theorem lookupPanFunction_sourceFunctionEntries_mem
    [BEq String] [LawfulBEq String]
    (declarations : List (Decl α))
    (name : FunName) (parameters : List VarName) (body : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (parameters, body)) :
    (name, parameters, body) ∈ sourceFunctionEntries declarations := by
  induction declarations with
  | nil =>
      simp [sourceFunctionEntries, lookupPanFunction] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name = declaration.name
          · have hpair :
                (declaration.params.map Prod.fst, declaration.body) =
                  (parameters, body) := by
                exact Option.some.inj (by
                  simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                    hlookup)
            cases hpair
            simp [sourceFunctionEntries, hname]
          · have htail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (parameters, body) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                  hlookup
            exact List.mem_cons_of_mem _ (ih htail)
      | decl shape declaration value =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (parameters, body) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          simpa [sourceFunctionEntries] using (ih htail)
      | exnDecl exception shape =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (parameters, body) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          simpa [sourceFunctionEntries] using (ih htail)
      | name struct fields =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (parameters, body) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          simpa [sourceFunctionEntries] using (ih htail)

theorem sourceFunctionEntries_localised_of_lookup
    [BEq String] [LawfulBEq String]
    (declarations : List (Decl α))
    (hlocalised : panValuePcLocalisedCode (sourceFunctionEntries declarations))
    (name : FunName) (parameters : List VarName) (body : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (parameters, body)) :
    localisedProg body := by
  exact hlocalised (name, parameters, body)
    (lookupPanFunction_sourceFunctionEntries_mem declarations name parameters body
      hlookup)

/-! Keep the source lookup and the function-info lookup on the same
    declaration.  This is important in the presence of malformed duplicate
    names: the target compiled lookup and the source metadata must not be
    assembled from two independent existential witnesses. -/
theorem lookupCompiledFunction_compileFunctions_with_info_of_source_lookup
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) ∧
      lookupCompiledFunction name (compileFunctions context declarations) =
        some ((compileParamVars declaration.params 0).2.1,
          compileProg
            { context with
                vars := panToCrepMakeVmap declaration.params
                maxVar := (compileParamVars declaration.params 0).2.2 }
            declaration.body) := by
  induction declarations with
  | nil =>
      simp [sourceFunctionEntries, lookupPanFunction] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name = declaration.name
          · have hpair :
                (declaration.params.map Prod.fst, declaration.body) =
                  (sourceParams, sourceBody) := by
                exact Option.some.inj (by
                  simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                    hlookup)
            cases hpair
            refine ⟨declaration, hname.symm, rfl, rfl, ?_, ?_⟩
            · simp [functionInfos, panToCrepMakeFuncs, lookupInfo, hname]
            · simpa [hname] using
                (lookupCompiledFunction_compileFunctions_head
                  context declaration declarations)
          · have htail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (sourceParams, sourceBody) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                  hlookup
            obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
              hfoundCompiled⟩ := ih htail
            refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
            · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo,
                Ne.symm hname] using hfoundInfo
            · have hcompiledName : name ≠ (compileFunDecl context declaration).name := by
                simpa [compileFunDecl] using hname
              exact lookupCompiledFunction_compileFunctions_skip_nonmatching
                context declaration declarations name
                (compileParamVars found.params 0).2.1
                (compileProg
                  { context with
                      vars := panToCrepMakeVmap found.params
                      maxVar := (compileParamVars found.params 0).2.2 }
                  found.body)
                hcompiledName hfoundCompiled
      | decl shape declaration value =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctions_skip_nonfunction
              context (.decl shape declaration value) declarations name
              (compileParamVars found.params 0).2.1
              (compileProg
                { context with
                    vars := panToCrepMakeVmap found.params
                    maxVar := (compileParamVars found.params 0).2.2 }
                found.body)
              (by intro function; simp) hfoundCompiled
      | exnDecl exception shape =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctions_skip_nonfunction
              context (.exnDecl exception shape) declarations name
              (compileParamVars found.params 0).2.1
              (compileProg
                { context with
                    vars := panToCrepMakeVmap found.params
                    maxVar := (compileParamVars found.params 0).2.2 }
                found.body)
              (by intro function; simp) hfoundCompiled
      | name struct fields =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctions_skip_nonfunction
              context (.name struct fields) declarations name
              (compileParamVars found.params 0).2.1
              (compileProg
                { context with
                    vars := panToCrepMakeVmap found.params
                    maxVar := (compileParamVars found.params 0).2.2 }
                found.body)
              (by intro function; simp) hfoundCompiled

theorem lookupCompiledFunction_compileToCrepe_with_info_of_source_lookup
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) ∧
      lookupCompiledFunction name (compileToCrepe context declarations) =
        some ((compileParamVars declaration.params 0).2.1,
          compileProg
            { context with
                functions := functionInfos declarations
                vars := panToCrepMakeVmap declaration.params
                maxVar := (compileParamVars declaration.params 0).2.2 }
            declaration.body) := by
  obtain ⟨declaration, hname, hparams, hbody, hinfo, hcompiled⟩ :=
    lookupCompiledFunction_compileFunctions_with_info_of_source_lookup
      ({ context with functions := functionInfos declarations }) declarations
      name sourceParams sourceBody hlookup
  refine ⟨declaration, hname, hparams, hbody, hinfo, ?_⟩
  simpa [compileToCrepe] using hcompiled

theorem lookupCompiledFunction_compileFunctionsSource_skip_nonmatching
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α)
    (declarations : List (Decl α)) (name : FunName)
    (parameters : List Nat) (body : CrepProg α)
    (hname : name ≠ declaration.name)
    (hlookup : lookupCompiledFunction name
        (compileFunctionsSource context declarations) = some (parameters, body)) :
    lookupCompiledFunction name
        (compileFunctionsSource context (.function declaration :: declarations)) =
      some (parameters, body) := by
  have hname' : name ≠ (compileFunDeclSource context declaration).name := by
    simpa [compileFunDeclSource] using hname
  simp [compileFunctionsSource, lookupCompiledFunction, hname', hlookup]

theorem lookupCompiledFunction_compileFunctionsSource_skip_nonfunction
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : Decl α)
    (declarations : List (Decl α)) (name : FunName)
    (parameters : List Nat) (body : CrepProg α)
    (hnonfunction : ∀ function : FunDecl α,
      declaration ≠ .function function)
    (hlookup : lookupCompiledFunction name
        (compileFunctionsSource context declarations) = some (parameters, body)) :
    lookupCompiledFunction name
        (compileFunctionsSource context (declaration :: declarations)) =
      some (parameters, body) := by
  cases declaration with
  | function declaration =>
      exact False.elim (hnonfunction declaration rfl)
  | decl shape declaration value =>
      simpa [compileFunctionsSource] using hlookup
  | exnDecl exception shape =>
      simpa [compileFunctionsSource] using hlookup
  | name struct fields =>
      simpa [compileFunctionsSource] using hlookup

theorem lookupCompiledFunction_compileFunctionsSource_head
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α)
    (declarations : List (Decl α)) :
    lookupCompiledFunction declaration.name
      (compileFunctionsSource context (.function declaration :: declarations)) =
      some (panToCrepVars declaration.params,
        panToCrepCompFunc context declaration.params declaration.body) := by
  simp [compileFunctionsSource, compileFunDeclSource, lookupCompiledFunction]

theorem lookupCompiledFunction_compileFunctionsSource_with_info_of_source_lookup
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) ∧
      lookupCompiledFunction name (compileFunctionsSource context declarations) =
        some (panToCrepVars declaration.params,
          panToCrepCompFunc context declaration.params declaration.body) := by
  induction declarations with
  | nil =>
      simp [sourceFunctionEntries, lookupPanFunction] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name = declaration.name
          · have hpair :
                (declaration.params.map Prod.fst, declaration.body) =
                  (sourceParams, sourceBody) := by
                exact Option.some.inj (by
                  simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                    hlookup)
            cases hpair
            refine ⟨declaration, hname.symm, rfl, rfl, ?_, ?_⟩
            · simp [functionInfos, panToCrepMakeFuncs, lookupInfo, hname]
            · simpa [hname] using
                (lookupCompiledFunction_compileFunctionsSource_head
                  context declaration declarations)
          · have htail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (sourceParams, sourceBody) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                  hlookup
            obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
              hfoundCompiled⟩ := ih htail
            refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
            · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo,
                Ne.symm hname] using hfoundInfo
            · exact lookupCompiledFunction_compileFunctionsSource_skip_nonmatching
                context declaration declarations name
                (panToCrepVars found.params)
                (panToCrepCompFunc context found.params found.body)
                hname hfoundCompiled
      | decl shape declaration value =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctionsSource_skip_nonfunction
              context (.decl shape declaration value) declarations name
              (panToCrepVars found.params)
              (panToCrepCompFunc context found.params found.body)
              (by intro function; simp) hfoundCompiled
      | exnDecl exception shape =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctionsSource_skip_nonfunction
              context (.exnDecl exception shape) declarations name
              (panToCrepVars found.params)
              (panToCrepCompFunc context found.params found.body)
              (by intro function; simp) hfoundCompiled
      | name struct fields =>
          have htail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo,
            hfoundCompiled⟩ := ih htail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_, ?_⟩
          · simpa [functionInfos, panToCrepMakeFuncs, lookupInfo] using hfoundInfo
          · exact lookupCompiledFunction_compileFunctionsSource_skip_nonfunction
              context (.name struct fields) declarations name
              (panToCrepVars found.params)
              (panToCrepCompFunc context found.params found.body)
              (by intro function; simp) hfoundCompiled

theorem lookupCompiledFunction_compileToCrep_with_info_of_source_lookup
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) ∧
      lookupCompiledFunction name (compileToCrep context declarations) =
        some (panToCrepVars declaration.params,
          panToCrepCompFunc
            { context with functions := functionInfos declarations }
            declaration.params declaration.body) := by
  obtain ⟨declaration, hname, hparams, hbody, hinfo, hcompiled⟩ :=
    lookupCompiledFunction_compileFunctionsSource_with_info_of_source_lookup
      ({ context with functions := functionInfos declarations }) declarations
      name sourceParams sourceBody hlookup
  refine ⟨declaration, hname, hparams, hbody, hinfo, ?_⟩
  simpa [compileToCrep] using hcompiled

/-! Concrete source-table instance of `panValuePcCodeRelConcrete`. -/
theorem panValuePcCodeRelConcrete_compileToCrep
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hlocalised : panValuePcLocalisedCode (sourceFunctionEntries declarations)) :
    panValuePcCodeRelConcrete
      { context with functions := functionInfos declarations }
      (sourceFunctionEntries declarations)
      (compileToCrep context declarations) := by
  intro name parameters body hlookup
  obtain ⟨declaration, hname, hparams, hbody, hinfo, hcompiled⟩ :=
    lookupCompiledFunction_compileToCrep_with_info_of_source_lookup
      context declarations name parameters body hlookup
  refine ⟨sourceFunctionEntries_localised_of_lookup declarations hlocalised
      name parameters body hlookup, declaration.params, declaration.returnShape,
    ?_, ?_, ?_⟩
  · simpa using hinfo
  · simpa using hparams
  · subst body
    simpa using hcompiled

end Flapjack
