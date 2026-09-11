import Flapjack.CompileFunctionLookup

/-!
Correspondence between source and compiled function tables.

The source evaluator stores formal names, while the compiled table stores the
flattened slot vector.  The theorem below follows the same declaration list
and recovers the compiled entry for any successful source lookup.  The fixed
compilation context is intentional: compiling a tail must still see all
function signatures, including declarations before that tail.
-/

namespace Flapjack

def sourceFunctionEntries : List (Decl α) →
    List (FunName × List VarName × Prog α)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, declaration.params.map Prod.fst, declaration.body) ::
        sourceFunctionEntries declarations
  | _ :: declarations => sourceFunctionEntries declarations

theorem lookupCompiledFunction_compileFunctions_of_source_lookup
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupCompiledFunction name (compileFunctions context declarations) =
        some ((compileParamVars declaration.params 0).2.1,
          compileProg
            { context with
                vars := (compileParamVars declaration.params 0).1
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
            refine ⟨declaration, hname.symm, rfl, rfl, ?_⟩
            simpa [hname] using
              (lookupCompiledFunction_compileFunctions_head
                context declaration declarations)
          · have hlookupTail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (sourceParams, sourceBody) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                  hlookup
            obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundLookup⟩ :=
              ih hlookupTail
            refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
            have hcompiledName : name ≠ (compileFunDecl context declaration).name := by
              simpa [compileFunDecl] using hname
            exact lookupCompiledFunction_compileFunctions_skip_nonmatching
              context declaration declarations name
              (compileParamVars found.params 0).2.1
              (compileProg
                { context with
                    vars := (compileParamVars found.params 0).1
                    maxVar := (compileParamVars found.params 0).2.2 }
                found.body)
              hcompiledName hfoundLookup
      | decl shape declaration value =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundLookup⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [compileFunctions] using hfoundLookup
      | exnDecl exception shape =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundLookup⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [compileFunctions] using hfoundLookup
      | name struct fields =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundLookup⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [compileFunctions] using hfoundLookup

theorem lookupCompiledFunction_compileToCrepe_of_source_lookup
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
        some ((compileParamVars declaration.params 0).2.1,
          compileProg
            { context with
                functions := functionInfos declarations
                vars := (compileParamVars declaration.params 0).1
                maxVar := (compileParamVars declaration.params 0).2.2 }
            declaration.body) := by
  obtain ⟨declaration, hname, hparams, hbody, hcompiled⟩ :=
    lookupCompiledFunction_compileFunctions_of_source_lookup
      ({ context with functions := functionInfos declarations }) declarations
      name sourceParams sourceBody hlookup
  refine ⟨declaration, hname, hparams, hbody, ?_⟩
  simpa [compileToCrepe] using hcompiled

theorem lookupInfo_functionInfos_of_source_lookup
    [LawfulBEq String]
    (declarations : List (Decl α))
    (name : FunName) (sourceParams : List VarName) (sourceBody : Prog α)
    (hlookup : lookupPanFunction name (sourceFunctionEntries declarations) =
      some (sourceParams, sourceBody)) :
    ∃ declaration : FunDecl α,
      declaration.name = name ∧
      declaration.params.map Prod.fst = sourceParams ∧
      declaration.body = sourceBody ∧
      lookupInfo name (functionInfos declarations) =
        some (declaration.params, declaration.returnShape) := by
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
            refine ⟨declaration, hname.symm, rfl, rfl, ?_⟩
            simp [functionInfos, lookupInfo, hname]
          · have hlookupTail :
                lookupPanFunction name (sourceFunctionEntries declarations) =
                  some (sourceParams, sourceBody) := by
                simpa [sourceFunctionEntries, lookupPanFunction, hname] using
                  hlookup
            obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo⟩ :=
              ih hlookupTail
            refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
            simpa [functionInfos, lookupInfo, Ne.symm hname] using hfoundInfo
      | decl shape declaration value =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [functionInfos] using hfoundInfo
      | exnDecl exception shape =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [functionInfos] using hfoundInfo
      | name struct fields =>
          have hlookupTail :
              lookupPanFunction name (sourceFunctionEntries declarations) =
                some (sourceParams, sourceBody) := by
            simpa [sourceFunctionEntries, lookupPanFunction] using hlookup
          obtain ⟨found, hfoundName, hfoundParams, hfoundBody, hfoundInfo⟩ :=
            ih hlookupTail
          refine ⟨found, hfoundName, hfoundParams, hfoundBody, ?_⟩
          simpa [functionInfos] using hfoundInfo

theorem lookupInfo_functionInfos_of_source_lookup_eq
    [LawfulBEq String]
    (declarations : List (Decl α))
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
      declaration.returnShape = returnShape := by
  obtain ⟨declaration, hname, hparams, hbody, hdeclarationInfo⟩ :=
    lookupInfo_functionInfos_of_source_lookup declarations name sourceParams sourceBody
      hlookup
  have hpair :
      (declaration.params, declaration.returnShape) = (parameters, returnShape) := by
    exact Option.some.inj (hdeclarationInfo.symm.trans hinfo)
  cases hpair
  exact ⟨declaration, hname, hparams, hbody, rfl, rfl⟩

end Flapjack
