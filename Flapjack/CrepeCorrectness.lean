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

theorem compile_full_add_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress left right : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 10 state
        (compileProg context
          (.return (.op .add [.const left, .const right]))) =
      evalPanMemResult locals state.memory
        (.return (.op .add [.const left, .const right]) : Prog α) := by
  simp [compileProg, compileExp, compileExp.compileExpList, cexpHeads,
    evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemExp, evalPanBinOp]

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

theorem compile_full_ite_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress condition thenValue elseValue : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.ite (.const condition)
            (.return (.const thenValue))
            (.return (.const elseValue)))) =
      evalPanMemResult locals state.memory
        (.ite (.const condition)
          (.return (.const thenValue))
          (.return (.const elseValue))) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemCondition, evalPanMemExp]
  split <;> simp_all [evalCrepFullProg, evalCrepFullExp,
    evalPanMemProg, evalPanMemCondition, evalPanMemExp]

theorem compile_full_local_assign_return_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat) (value : α)
    (lookup : lookupInfo name context.vars = some (.one, [slot])) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))) =
      evalPanMemResult locals state.memory
        (.seq (.assign .local name (.const value))
          (.return (.var .local name))) := by
  simp [compileProg, compileExp, crepNestedSeq, lookup,
    evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanMemResult, evalPanMemProg,
    evalPanMemExp, updateCrepLocal, updatePanLocal,
    distinctLists]

theorem compile_full_local_return_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (environment_agrees : state.locals slot = locals name) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 5 state
        (compileProg context (.return (.var .local name))) =
      evalPanMemResult locals state.memory
        (.return (.var .local name) : Prog α) := by
  simp [compileProg, compileExp, lookup, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanMemResult, evalPanMemProg, evalPanMemExp,
    environment_agrees]
  cases h : locals name <;> simp [h]

end Flapjack
