import Flapjack.CompileCalleeParameterStateRelation

/-!
Lookup equations for the compiled function table.

The head equation is already enough for a single declaration.  This module
adds the nonmatching-tail step and the corresponding `compileToCrepe` form so
function lookup proofs can proceed through a declaration list without
unfolding the table compiler at every call site.
-/

namespace Flapjack

theorem lookupCompiledFunction_compileFunctions_skip_nonmatching
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α)
    (declarations : List (Decl α)) (name : FunName)
    (parameters : List Nat) (body : CrepProg α)
    (hname : name ≠ declaration.name)
    (hlookup : lookupCompiledFunction name
        (compileFunctions context declarations) = some (parameters, body)) :
    lookupCompiledFunction name
        (compileFunctions context (.function declaration :: declarations)) =
      some (parameters, body) := by
  have hname' : name ≠ (compileFunDecl context declaration).name := by
    simpa [compileFunDecl] using hname
  simp [compileFunctions, lookupCompiledFunction, hname', hlookup]

theorem lookupCompiledFunction_compileFunctions_skip_nonfunction
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : Decl α)
    (declarations : List (Decl α)) (name : FunName)
    (parameters : List Nat) (body : CrepProg α)
    (hnonfunction : ∀ function : FunDecl α,
      declaration ≠ .function function)
    (hlookup : lookupCompiledFunction name
        (compileFunctions context declarations) = some (parameters, body)) :
    lookupCompiledFunction name
        (compileFunctions context (declaration :: declarations)) =
      some (parameters, body) := by
  cases declaration with
  | function declaration =>
      exact False.elim (hnonfunction declaration rfl)
  | decl shape declaration value =>
      simpa [compileFunctions] using hlookup
  | exnDecl exception shape =>
      simpa [compileFunctions] using hlookup
  | name struct fields =>
      simpa [compileFunctions] using hlookup

theorem lookupCompiledFunction_compileToCrepe_head
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α)
    (declarations : List (Decl α)) :
    lookupCompiledFunction declaration.name
      (compileToCrepe context (.function declaration :: declarations)) =
      some ((compileParamVars declaration.params 0).2.1,
        compileProg
          { context with
              functions := functionInfos (.function declaration :: declarations)
              vars := (compileParamVars declaration.params 0).1
              maxVar := (compileParamVars declaration.params 0).2.2 }
          declaration.body) := by
  simpa [compileToCrepe] using
    (lookupCompiledFunction_compileFunctions_head
      ({ context with functions := functionInfos (.function declaration :: declarations) })
      declaration declarations)

end Flapjack
