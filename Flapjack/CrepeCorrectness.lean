import Flapjack.CrepeSemantics

/-!
Initial generic correctness lemmas for the stateful Crepe evaluator.

These statements deliberately quantify over all semantic handlers: the
programs involved do not invoke them, so the lemmas establish a clean
source-to-Crepe result boundary before adding hypotheses for calls, memory,
and FFI.
-/

namespace Flapjack

theorem compile_full_skip_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.skip : Prog α)) =
      evalPanMemResult locals state.memory (.skip : Prog α) := by
  simp [compileProg, evalCrepFullResult, evalCrepFullProg,
    evalPanMemResult, evalPanMemProg]

theorem compile_full_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress value : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.return (.const value))) =
      evalPanMemResult locals state.memory
        (.return (.const value) : Prog α) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemExp]

theorem compile_full_store_load_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress address value : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.store (.const address) (.const value))
            (.return (.load .one (.const address))))) =
      evalPanMemResult locals state.memory
        (.seq (.store (.const address) (.const value))
          (.return (.load .one (.const address)))) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    loadShape, evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanMemResult, evalPanMemProg, evalPanMemExp,
    updateMemory, updateCrepLocal, restoreCrepResult, restoreCrepLocal]

end Flapjack
