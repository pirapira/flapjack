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

end Flapjack
