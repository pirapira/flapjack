import Flapjack.CrepeSemantics
import Flapjack.PanProgramSemantics

/-!
Initial generic correctness lemmas for the stateful Crepe evaluator.

These statements deliberately quantify over all semantic handlers: the
programs involved do not invoke them, so the lemmas establish a clean
source-to-Crepe result boundary before adding hypotheses for calls, memory,
and FFI.
-/

namespace Flapjack

theorem compile_full_skip_compat_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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

/-! The first compact correctness leaf at the global-aware evaluator
    boundary.  `skip` leaves the separately threaded global environment
    unchanged, so its observable result remains the source memory result. -/
theorem compile_full_skip_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.skip : Prog α)) =
      evalPanMemResult locals state.memory (.skip : Prog α) := by
  simp [compileProg, evalCrepFullResultState, evalCrepFullProgState,
    evalPanMemResult, evalPanMemProg]

theorem compile_full_return_const_compat_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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

theorem compile_full_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress value : α) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.return (.const value))) =
      evalPanMemResult locals state.memory
        (.return (.const value) : Prog α) := by
  simp [compileProg, compileExp, evalCrepFullResultState,
    evalCrepFullProgState, evalCrepFullExpsState, evalCrepFullExpState,
    evalPanMemResult, evalPanMemProg, evalPanMemExp]

theorem compile_full_add_const_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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

theorem compile_full_add_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress left right : α) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 10 state
        (compileProg context
          (.return (.op .add [.const left, .const right]))) =
      evalPanMemResult locals state.memory
        (.return (.op .add [.const left, .const right]) : Prog α) := by
  simp [compileProg, compileExp, compileExp.compileExpList, cexpHeads,
    evalCrepFullResultState, evalCrepFullProgState,
    evalCrepFullExpsState, evalCrepFullExpState, evalPanMemResult,
    evalPanMemProg, evalPanMemExp, evalPanBinOp]

theorem compile_full_store_load_const_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    updateMemory, updateCrepLocal, restoreCrepResult]

theorem compile_full_store_load_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress address value : α) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.store (.const address) (.const value))
            (.return (.load .one (.const address))))) =
      evalPanMemResult locals state.memory
        (.seq (.store (.const address) (.const value))
          (.return (.load .one (.const address)))) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    loadShape, evalCrepFullResultState, evalCrepFullProgState,
    evalCrepFullExpsState, evalCrepFullExpState, evalPanMemResult,
    evalPanMemProg, evalPanMemExp, updateMemory, updateCrepLocal,
    restoreCrepResult]

theorem compile_full_ite_const_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
  split <;> simp_all [
    ]

theorem compile_full_ite_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress condition thenValue elseValue : α) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.ite (.const condition)
            (.return (.const thenValue))
            (.return (.const elseValue)))) =
      evalPanMemResult locals state.memory
        (.ite (.const condition)
          (.return (.const thenValue))
          (.return (.const elseValue))) := by
  simp [compileProg, compileExp, evalCrepFullResultState,
    evalCrepFullProgState, evalCrepFullExpsState, evalCrepFullExpState,
    evalPanMemResult, evalPanMemProg, evalPanMemCondition,
    evalPanMemExp]
  split <;> simp_all

theorem compile_full_local_assign_return_const_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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

theorem compile_full_local_assign_return_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat) (value : α)
    (lookup : lookupInfo name context.vars = some (.one, [slot])) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))) =
      evalPanMemResult locals state.memory
        (.seq (.assign .local name (.const value))
          (.return (.var .local name))) := by
  simp [compileProg, compileExp, crepNestedSeq, lookup,
    evalCrepFullResultState, evalCrepFullProgState, evalCrepFullExpsState,
    evalCrepFullExpState, evalPanMemResult, evalPanMemProg,
    evalPanMemExp, updateCrepLocal, updatePanLocal, distinctLists]

theorem compile_full_local_return_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
  cases h : locals name <;> simp []

theorem compile_full_local_return_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (environment_agrees : state.locals slot = locals name) :
    evalCrepFullResultState [] primitive ffi sharedMem
        baseAddress topAddress 5 state
        (compileProg context (.return (.var .local name))) =
      evalPanMemResult locals state.memory
        (.return (.var .local name) : Prog α) := by
  simp [compileProg, compileExp, lookup, evalCrepFullResultState,
    evalCrepFullProgState, evalCrepFullExpsState, evalCrepFullExpState,
    evalPanMemResult, evalPanMemProg, evalPanMemExp, environment_agrees]
  cases h : locals name <;> simp []

theorem compile_full_extCall_const_noop_compat_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress configuration configurationLength array arrayLength : α)
    (function : FunName) :
    evalCrepFullProg [] primitive
        (fun _ _ _ _ _ sourceState => some sourceState) sharedMem
        baseAddress topAddress 30 state
        (compileProg context
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength))) =
      some (.normal state) ∧
    evalPanFfiProg
        (fun _ _ _ _ _ sourceLocals => some sourceLocals) locals
        (.extCall function (.const configuration)
          (.const configurationLength) (.const array) (.const arrayLength)) =
      some locals := by
  have hrestoreFour (base : Nat → Option α) (offset : Nat)
      (value1 value2 value3 value4 : α) :
      restoreCrepLocal
          (restoreCrepLocal
            (restoreCrepLocal
              (restoreCrepLocal
                (updateCrepLocal
                  (updateCrepLocal
                    (updateCrepLocal (updateCrepLocal base (offset + 1) value1)
                      (offset + 2) value2)
                    (offset + 3) value3)
                  (offset + 4) value4)
                (offset + 4) (base (offset + 4)))
              (offset + 3) (base (offset + 3)))
            (offset + 2) (base (offset + 2)))
          (offset + 1) (base (offset + 1)) = base := by
    funext current
    by_cases h1 : current = offset + 1
    · simp [restoreCrepLocal, h1]
    by_cases h2 : current = offset + 2
    · simp [restoreCrepLocal, h2]
    by_cases h3 : current = offset + 3
    · simp [restoreCrepLocal, h3]
    by_cases h4 : current = offset + 4
    · simp [restoreCrepLocal, h4]
    · simp [restoreCrepLocal, updateCrepLocal, h1, h2, h3, h4]
  simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
    evalCrepFullProg, evalCrepFullExp, evalPanExp, evalPanFfiProg, evalPanExtCall,
    updateCrepLocal, restoreCrepResult, hrestoreFour]

theorem compile_full_extCall_const_noop_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress configuration configurationLength array arrayLength : α)
    (function : FunName) :
    evalCrepFullProgState [] primitive
        (fun _ _ _ _ _ sourceState => some (.returned sourceState)) sharedMem
        baseAddress topAddress 30 state
        (compileProg context
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength))) =
      some (.normal state) := by
  have hrestoreFour (base : Nat → Option α) (offset : Nat)
      (value1 value2 value3 value4 : α) :
      restoreCrepLocal
          (restoreCrepLocal
            (restoreCrepLocal
              (restoreCrepLocal
                (updateCrepLocal
                  (updateCrepLocal
                    (updateCrepLocal (updateCrepLocal base (offset + 1) value1)
                      (offset + 2) value2)
                    (offset + 3) value3)
                  (offset + 4) value4)
                (offset + 4) (base (offset + 4)))
              (offset + 3) (base (offset + 3)))
            (offset + 2) (base (offset + 2)))
          (offset + 1) (base (offset + 1)) = base := by
    funext current
    by_cases h1 : current = offset + 1
    · simp [restoreCrepLocal, h1]
    by_cases h2 : current = offset + 2
    · simp [restoreCrepLocal, h2]
    by_cases h3 : current = offset + 3
    · simp [restoreCrepLocal, h3]
    by_cases h4 : current = offset + 4
    · simp [restoreCrepLocal, h4]
    · simp [restoreCrepLocal, updateCrepLocal, h1, h2, h3, h4]
  simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
    evalCrepFullProgState, evalCrepFullExpState, updateCrepLocal,
    restoreCrepResult, hrestoreFour]

/-! A first structured source-to-Crep boundary for the correctness theorem.
    A closed word return has the same observable flattened result in the
    structured Pancake evaluator and in the full Crepe evaluator.  Keeping
    the source result in its structured form makes this lemma composable with
    the later environment and memory relations. -/
theorem compile_full_pan_value_return_word_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord value : α) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 1 state
        (compileProg context (.return (.const value))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.return (.const value))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanValueProg,
    evalPanValueProgWithPrimitive, evalPanValueExp, panValueFlatWords,
    panValueFlatWordsFuel]

/-! The return boundary is also useful with a non-constant source expression.
    Its two hypotheses are precisely the source-expression and lowered-Crep
    expression obligations that a later expression pass theorem supplies. -/
theorem compile_full_pan_value_return_word_of_exp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord value : α)
    (expression : Exp α) (compiled : CrepExp α)
    (hsource : evalPanValueExp structs locals globals (fun address =>
      (state.memory address).map PanValue.word)
      baseAddress topAddress bytesInWord expression = some (.word value))
    (hcompile : compileExp context expression = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory baseAddress topAddress
      compiled = some value) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 1 state
        (compileProg context (.return expression)) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.return expression)).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [compileProg, hcompile, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, hcompiled, evalPanValueProg,
    evalPanValueProgWithPrimitive, hsource, panValueFlatWords,
    panValueFlatWordsFuel]

/-! Shape-preserving local assignment is the next stateful source boundary.
    The source variable is already bound to a word, so CakeML's assignment
    validity check and the flattened Crep slot update can be related directly. -/
theorem compile_full_pan_value_local_assign_return_word_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slot : Nat) (oldValue value : α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hlocals : locals name = some (.word oldValue)) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 20 state
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.seq (.assign .local name (.const value))
          (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [compileProg, compileExp, hlookup, hlocals, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanValueProg, evalPanValueProgWithPrimitive, evalPanValueExp,
    panValueAssignmentValid, panValueShape, panShapeMatches,
    crepNestedSeq, distinctLists, updateCrepLocal, updatePanValueMap,
    panValueFlatWords,
    panValueFlatWordsFuel]

/-! Sequence evaluation can now be composed at the structured source boundary.
    The first component is required to complete normally in both semantics;
    the continuation hypothesis is then reusable for any source statement.
    This explicit state-threaded form is the induction interface needed for a
    full Pancake-to-Crep simulation theorem. -/
theorem compile_full_pan_value_seq_normal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (firstSourceLocals firstSourceGlobals : VarName → Option (PanValue α))
    (firstSourceMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (hfirstSource : evalPanValueProg structs baseAddress topAddress bytesInWord
      sourceLocals sourceGlobals sourceMemory first =
        some (firstSourceLocals, firstSourceGlobals, firstSourceMemory, []))
    (hfirstCrep : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state (compileProg context first) =
        some (.normal firstState))
    (hsecond : evalCrepFullResult [] primitive ffi sharedMem
      baseAddress topAddress fuel firstState (compileProg context second) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        firstSourceLocals firstSourceGlobals firstSourceMemory second).map
        (fun result => result.2.2.2.flatMap panValueFlatWords)) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state (compileProg context (.seq first second)) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        sourceLocals sourceGlobals sourceMemory (.seq first second)).map
    (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp only [compileProg, evalCrepFullResult, evalCrepFullProg]
  rw [hfirstCrep]
  change (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress fuel
      firstState (compileProg context second)).bind (fun result =>
        match result with
        | .returned _ values => some values
        | .normal _ => some []
        | .raised _ _ | .broke _ _ | .continued _ _ | .finalFfi _ _ => none) = _
  have hsecond' :
      (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress fuel
        firstState (compileProg context second)).bind (fun result =>
          match result with
          | .returned _ values => some values
          | .normal _ => some []
          | .raised _ _ | .broke _ _ | .continued _ _ | .finalFfi _ _ => none) =
        (evalPanValueProg structs baseAddress topAddress bytesInWord
          firstSourceLocals firstSourceGlobals firstSourceMemory second).map
          (fun result => result.2.2.2.flatMap panValueFlatWords) := by
    exact hsecond
  rw [hsecond']
  have hfirstSource' :
      evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        sourceLocals sourceGlobals sourceMemory (fun _ _ => none) first =
        some (firstSourceLocals, firstSourceGlobals, firstSourceMemory, []) := by
    simpa [evalPanValueProg] using hfirstSource
  simp only [evalPanValueProg]
  simp only [evalPanValueProgWithPrimitive]
  rw [hfirstSource']
  simp

/-! The source return boundary is not intrinsically word-shaped.  This
    structured form is the one needed for record-valued Pancake expressions:
    the compiler emits the flattened Crep words, while the source evaluator
    retains the original structured value until the final observation. -/
theorem compile_full_pan_value_return_of_exp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (expression : Exp α)
    (value : PanValue α) (compiled : List (CrepExp α))
    (hsource : evalPanValueExp structs locals globals (fun address =>
      (state.memory address).map PanValue.word)
      baseAddress topAddress bytesInWord expression = some value)
    (hvalid : panValuePayloadWithinLimit structs value = true)
    (hcompile : compileExp context expression =
      (compiled, panValueShape structs value))
    (hcompiled : evalCrepFullExps state.locals state.memory baseAddress topAddress
      compiled = some (panValueFlatWords value)) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 1 state
        (compileProg context (.return expression)) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.return expression)).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [compileProg, hcompile, evalCrepFullResult, evalCrepFullProg,
    hcompiled, evalPanValueProg,
    evalPanValueProgWithPrimitive, hsource, hvalid]

/-! A concrete structured witness for the preceding abstraction: a record of
    closed word constants is flattened by the real compiler and returned by
    the full Crep evaluator with the same words as the source semantics. -/
theorem compile_full_pan_value_record_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (values : List α)
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map PanValue.word)) = true) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 1 state
        (compileProg context
          (.return (.rStruct (values.map (fun value => .const value))))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.return (.rStruct (values.map (fun value => .const value))))).map
    (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hsourceExps : ∀ values : List α,
      evalPanValueExp.evalPanValueExps structs locals globals
        (fun address => (state.memory address).map PanValue.word)
        baseAddress topAddress bytesInWord
        (values.map (fun value => .const value)) =
      some (values.map PanValue.word) := by
    intro values
    induction values with
    | nil => simp [evalPanValueExp.evalPanValueExps]
    | cons value values ih =>
        simp [evalPanValueExp.evalPanValueExps, evalPanValueExp, ih]
  have hsource : evalPanValueExp structs locals globals (fun address =>
      (state.memory address).map PanValue.word)
      baseAddress topAddress bytesInWord
      (.rStruct (values.map (fun value => .const value))) =
      some (.rStruct (values.map PanValue.word)) := by
    simp only [evalPanValueExp]
    rw [hsourceExps values]
    rfl
  have hcompileExpList : ∀ values : List α,
      compileExp.compileExpList context
        (values.map (fun value => .const value)) =
      values.map (fun value => ([.const value], .one)) := by
    intro values
    induction values with
    | nil => simp [compileExp.compileExpList]
    | cons value values ih =>
        simp [compileExp.compileExpList, compileExp, ih]
  have hflatCompilePairs : ∀ values : List α,
      List.flatMap Prod.fst
          (values.map (fun value => ([CrepExp.const value], Shape.one))) =
        values.map (fun value => .const value) := by
    intro values
    induction values with
    | nil => rfl
    | cons value values ih => simp [ih]
  have hcompile : ∀ values : List α, compileExp context
      (.rStruct (values.map (fun value => .const value))) =
      (values.map (fun value => .const value),
        .comb (values.map (fun _ => .one))) := by
    intro values
    simp [compileExp, hcompileExpList, hflatCompilePairs,
      Function.comp_def]
  have hcompiled : ∀ values : List α, evalCrepFullExps state.locals state.memory
      baseAddress topAddress (values.map (fun value => .const value)) =
      some values := by
    intro values
    induction values with
    | nil => simp [evalCrepFullExps]
    | cons value values ih =>
        simp [evalCrepFullExps, evalCrepFullExp, ih]
  have hlistFuel : ∀ values : List α,
      panValueFlatValueFuel.panValueFlatValueListFuel
        (values.map PanValue.word) = values.length := by
    intro values
    induction values with
    | nil => simp [panValueFlatValueFuel.panValueFlatValueListFuel]
    | cons value values ih =>
        simp [panValueFlatValueFuel.panValueFlatValueListFuel,
          panValueFlatValueFuel, ih, Nat.add_comm]
  have hvalueFuel : ∀ values : List α,
      panValueFlatValueFuel (.rStruct (values.map PanValue.word)) =
        values.length + 1 := by
    intro values
    simp only [panValueFlatValueFuel]
    rw [hlistFuel values]
    simpa using (Nat.add_comm 1 values.length)
  have hwordsFuel : ∀ (fuel : Nat) (values : List α),
      values.length < fuel →
      panValueFlatWordsFuel.panValueFlatWordsListFuel fuel
          (values.map PanValue.word) = values := by
    intro fuel values
    induction values generalizing fuel with
    | nil => intro; simp [panValueFlatWordsFuel.panValueFlatWordsListFuel]
    | cons value values ih =>
        cases fuel with
        | zero => simp_all
        | succ fuel =>
            intro hlength
            cases fuel with
            | zero => simp_all
            | succ fuel =>
                simp only [List.length_cons] at hlength
                have htail : values.length < fuel + 1 := by omega
                simp [panValueFlatWordsFuel.panValueFlatWordsListFuel,
                  panValueFlatWordsFuel, ih (fuel + 1) htail]
  have hflat : ∀ values : List α,
      panValueFlatWords (.rStruct (values.map PanValue.word)) = values := by
    intro values
    rw [panValueFlatWords, hvalueFuel values]
    simp only [panValueFlatWordsFuel]
    exact hwordsFuel (2 * (values.length + 1)) values (by omega)
  exact compile_full_pan_value_return_of_exp context structs locals globals
    state primitive ffi sharedMem baseAddress topAddress bytesInWord
    (.rStruct (values.map (fun value => .const value)))
    (.rStruct (values.map PanValue.word))
    (values.map (fun value => .const value)) hsource hvalid
    (by simpa [panValueShape, Function.comp_def] using hcompile values)
    (by simpa [hflat values] using hcompiled values)

/-! The structured source boundary also covers branch selection.  This closed
    equality conditional exercises the source boolean interpretation and the
    compiled Crep nonzero test, while both branches retain word-shaped values. -/
theorem compile_full_pan_value_ite_word_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord conditionLeft conditionRight : α)
    (thenValue elseValue : α) (one_ne_zero : (1 : α) ≠ 0) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 20 state
        (compileProg context
          (.ite (.cmp .equal (.const conditionLeft) (.const conditionRight))
            (.return (.const thenValue)) (.return (.const elseValue)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.ite (.cmp .equal (.const conditionLeft) (.const conditionRight))
          (.return (.const thenValue)) (.return (.const elseValue)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  by_cases hcondition : conditionLeft == conditionRight
  · simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
      evalCrepFullExp, evalCrepFullExps, evalPanValueProg,
      evalPanValueProgWithPrimitive, evalPanValueExp,
      evalPanCmp, hcondition, one_ne_zero,
      panValueFlatWords, panValueFlatWordsFuel]
  · simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
      evalCrepFullExp, evalCrepFullExps, evalPanValueProg,
      evalPanValueProgWithPrimitive, evalPanValueExp,
      evalPanCmp, hcondition,
      panValueFlatWords, panValueFlatWordsFuel]

/-! Conditional correctness can be composed from an expression boundary and
    branch boundaries.  This is the induction-shaped theorem needed once
    condition expressions and branch programs are no longer closed constants. -/
theorem compile_full_pan_value_ite_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (conditionValue : α) (thenBranch elseBranch : Prog α)
    (hsourceCondition : evalPanValueExp structs locals globals (fun address =>
      (state.memory address).map PanValue.word)
      baseAddress topAddress bytesInWord condition = some (.word conditionValue))
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompiledCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some conditionValue)
    (hthen : evalCrepFullResult [] primitive ffi sharedMem
      baseAddress topAddress fuel state (compileProg context thenBranch) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word) thenBranch).map
        (fun result => result.2.2.2.flatMap panValueFlatWords))
    (helse : evalCrepFullResult [] primitive ffi sharedMem
      baseAddress topAddress fuel state (compileProg context elseBranch) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word) elseBranch).map
        (fun result => result.2.2.2.flatMap panValueFlatWords)) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (compileProg context (.ite condition thenBranch elseBranch)) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.ite condition thenBranch elseBranch)).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hcompile :
      compileProg context (.ite condition thenBranch elseBranch) =
        .ite compiledCondition (compileProg context thenBranch)
          (compileProg context elseBranch) := by
    simp [compileProg, hcompileCondition]
  rw [hcompile]
  simp only [evalCrepFullResult, evalCrepFullProg, hcompiledCondition,
    evalPanValueProg, evalPanValueProgWithPrimitive, hsourceCondition]
  by_cases hcondition : (conditionValue != 0) = true
  · simp [hcondition]
    simpa [evalCrepFullResult, evalPanValueProg] using hthen
  · simp [hcondition]
    simpa [evalCrepFullResult, evalPanValueProg] using helse

/-! A word declaration binds a fresh Crep slot while the source evaluator
    binds the named local, and both evaluators expose the same returned word.
    This is the base declaration case for the full source induction. -/
theorem compile_full_pan_value_dec_word_return_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord value : α) (name : VarName) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 10 state
        (compileProg context
          (.dec name .one (.const value)
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.dec name .one (.const value)
        (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [compileProg, compileExp, allocatedNames, nestedDecs,
    evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanValueProg, evalPanValueProgWithPrimitive,
    evalPanValueExp, updateCrepLocal, restoreCrepResult,
    updatePanValueMap, lookupInfo, panValueShape, panShapeMatches,
    panValueFlatWords, panValueFlatWordsFuel]

/-! A two-word record declaration gives a concrete structured witness for the
    declaration path: both flattened slots are allocated and returned in
    source order. -/
theorem compile_full_pan_value_dec_two_word_record_return_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord left right : α) (name : VarName) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 10 state
        (compileProg context
          (.dec name (.comb [.one, .one])
            (.rStruct [.const left, .const right])
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.dec name (.comb [.one, .one])
          (.rStruct [.const left, .const right])
          (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hcompile :
      compileExp context (.rStruct [.const left, .const right]) =
        ([.const left, .const right], .comb [.one, .one]) := by
    simp [compileExp, compileExp.compileExpList]
  have hnames :
      allocatedNames context (.comb [.one, .one]) =
        [context.maxVar + 1, context.maxVar + 2] := by
    simp [allocatedNames, Shape.shapeSize, List.range, List.range.loop]
  have hprogram :
      compileProg context
          (.dec name (.comb [.one, .one])
            (.rStruct [.const left, .const right])
            (.return (.var .local name))) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [.const left, .const right]
          (.return [.var (context.maxVar + 1), .var (context.maxVar + 2)]) := by
    simp only [compileProg, hcompile, Shape.shapeSize]
    rw [hnames]
    simp [compileExp, lookupInfo]
  have hsourceExps :
      evalPanValueExp.evalPanValueExps structs locals globals
        (fun address => (state.memory address).map PanValue.word)
        baseAddress topAddress bytesInWord [.const left, .const right] =
      some [.word left, .word right] := by
    simp [evalPanValueExp.evalPanValueExps, evalPanValueExp]
  rw [hprogram]
  have hflat :
      panValueFlatWords (.rStruct [.word left, .word right]) = [left, right] := by
    simp [panValueFlatWords, panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel]
  have hflatListFuel :
      panValueFlatWordsFuel.panValueFlatWordsListFuel
          (2 * panValueFlatValueFuel
            (PanValue.rStruct [PanValue.word left, PanValue.word right]))
          [PanValue.word left, PanValue.word right] = [left, right] := by
    simp [panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel]
  simp [nestedDecs,
    evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanValueProg, evalPanValueProgWithPrimitive,
    evalPanValueExp, updateCrepLocal, restoreCrepResult,
    updatePanValueMap, panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches,
    hsourceExps, hflatListFuel,
    panValueFlatWords, panValueFlatWordsFuel]

/-! The declaration boundary can be composed with an arbitrary source
    expression and continuation once the expression and continuation
    obligations are supplied separately.  This is the induction shape used
    by the full Pancake correctness theorem. -/
theorem compile_full_pan_value_dec_two_word_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord left right : α) (name : VarName)
    (body : Prog α) (expression : Exp α)
    (compiledLeft compiledRight : CrepExp α)
    (hsource : evalPanValueExp structs locals globals (fun address =>
      (state.memory address).map PanValue.word)
      baseAddress topAddress bytesInWord expression =
      some (.rStruct [.word left, .word right]))
    (hcompile : compileExp context expression =
      ([compiledLeft, compiledRight], .comb [.one, .one]))
    (hcompiledLeft : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledLeft = some left)
    (hcompiledRight : ∀ value : α, evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) value)
      state.memory baseAddress topAddress compiledRight = some right)
    (hbody : evalCrepFullResult [] primitive ffi sharedMem
      baseAddress topAddress 8
      { state with locals :=
          updateCrepLocal (updateCrepLocal state.locals
            (context.maxVar + 1) left) (context.maxVar + 2) right }
      (compileProg
        { context with
            vars := (name, (.comb [.one, .one],
              [context.maxVar + 1, context.maxVar + 2])) :: context.vars
            maxVar := context.maxVar + 2 }
        body) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        (updatePanValueMap locals name (.rStruct [.word left, .word right]))
        globals (fun address =>
          (state.memory address).map PanValue.word) body).map
        (fun result => result.2.2.2.flatMap panValueFlatWords)) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 10 state
        (compileProg context
          (.dec name (.comb [.one, .one]) expression body)) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.dec name (.comb [.one, .one]) expression body)).map
      (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hnames :
      allocatedNames context (.comb [.one, .one]) =
        [context.maxVar + 1, context.maxVar + 2] := by
    simp [allocatedNames, Shape.shapeSize, List.range, List.range.loop]
  have hprogram :
      compileProg context
          (.dec name (.comb [.one, .one]) expression body) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [compiledLeft, compiledRight]
          (compileProg
            { context with
                vars := (name, (.comb [.one, .one],
                  [context.maxVar + 1, context.maxVar + 2])) :: context.vars
                maxVar := context.maxVar + 2 }
          body) := by
    simp only [compileProg, hcompile, Shape.shapeSize]
    rw [hnames]
    simp
  rw [hprogram]
  have hcrepNested :
      evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 10 state
        (nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [compiledLeft, compiledRight]
          (compileProg
            { context with
                vars := (name, (.comb [.one, .one],
                  [context.maxVar + 1, context.maxVar + 2])) :: context.vars
                maxVar := context.maxVar + 2 }
            body)) =
      evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 8
        { state with locals :=
            updateCrepLocal (updateCrepLocal state.locals
              (context.maxVar + 1) left) (context.maxVar + 2) right }
        (compileProg
          { context with
              vars := (name, (.comb [.one, .one],
                [context.maxVar + 1, context.maxVar + 2])) :: context.vars
              maxVar := context.maxVar + 2 }
            body) := by
    simp only [nestedDecs, evalCrepFullResult, evalCrepFullProg,
      hcompiledLeft]
    simp [Option.bind, hcompiledRight]
    generalize hraw : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress 8
      { state with locals :=
          updateCrepLocal (updateCrepLocal state.locals
            (context.maxVar + 1) left) (context.maxVar + 2) right }
      (compileProg
        { context with
            vars := (name, (.comb [.one, .one],
              [context.maxVar + 1, context.maxVar + 2])) :: context.vars
            maxVar := context.maxVar + 2 }
        body) = raw
    cases raw with
    | none => simp
    | some result => cases result <;> simp [restoreCrepResult]
  rw [hcrepNested, hbody]
  simp [evalPanValueProg, evalPanValueProgWithPrimitive,
    hsource, panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches, Function.comp_def]
  cases hresult : evalPanValueProgWithPrimitive structs baseAddress topAddress
      bytesInWord
      (updatePanValueMap locals name (.rStruct [.word left, .word right]))
      globals (fun address => (state.memory address).map PanValue.word)
      (fun _ _ => none) body <;> simp

/-! A structured local assignment updates both flattened destination slots
    before the returned local is read.  This is the assignment case needed by
    the source correctness induction after declarations have introduced a
    shaped local. -/
theorem compile_full_pan_value_local_assign_record_return_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slotLeft slotRight : Nat)
    (oldLeft oldRight left right : α)
    (hlookup : lookupInfo name context.vars =
      some (.comb [.one, .one], [slotLeft, slotRight]))
    (hdistinct : slotLeft ≠ slotRight)
    (hlocals : locals name = some (.rStruct [.word oldLeft, .word oldRight])) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 30 state
        (compileProg context
          (.seq
            (.assign .local name
              (.rStruct [.const left, .const right]))
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun address =>
          (state.memory address).map PanValue.word)
        (.seq
          (.assign .local name
            (.rStruct [.const left, .const right]))
          (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hsourceExps :
      evalPanValueExp.evalPanValueExps structs locals globals
        (fun address => (state.memory address).map PanValue.word)
        baseAddress topAddress bytesInWord
        [.const left, .const right] =
      some [.word left, .word right] := by
    simp [evalPanValueExp.evalPanValueExps, evalPanValueExp]
  have hflatListFuel :
      panValueFlatWordsFuel.panValueFlatWordsListFuel
          (2 * panValueFlatValueFuel
            (PanValue.rStruct [PanValue.word left, PanValue.word right]))
          [PanValue.word left, PanValue.word right] = [left, right] := by
    simp [panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel]
  simp [compileProg, compileExp, compileExp.compileExpList, hlookup,
    hlocals, evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanValueProg, evalPanValueProgWithPrimitive,
    evalPanValueExp, panValueAssignmentValid, panValueShape,
    panShapeMatches, panShapeMatches.panShapeListMatches,
    crepNestedSeq, distinctLists, hdistinct, updateCrepLocal,
    updatePanValueMap, hsourceExps, hflatListFuel,
    panValueFlatWords, panValueFlatWordsFuel]

/-! A word store followed by a shaped load exercises the same flat-memory
    update on both sides of the source-to-Crep boundary. -/
theorem compile_full_pan_value_store_load_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord address value : α) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 80 state
        (compileProg context
          (.seq
            (.store (.const address) (.const value))
            (.return (.load .one (.const address))))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun current =>
          (state.memory current).map PanValue.word)
        (.seq
          (.store (.const address) (.const value))
          (.return (.load .one (.const address))))).map
    (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [Option.bind, compileProg, compileExp, freshNames,
    nestedDecs, crepNestedSeq, stores, loadShape, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    restoreCrepResult,
    evalPanValueProg, evalPanValueProgWithPrimitive, evalPanValueExp,
    panValueFlatLoad, panValueFlatLoadFuel,
    panValueFlatReadWord,
    panValueStoreWithAccess, panValueFlatStoreWords,
    updateCrepLocal, updateMemory, updatePanValueMemory, updatePanValueMap,
    isWfShape,
    panValueFlatWords, panValueFlatWordsFuel]

/-! A structured two-word store followed by a shaped load exercises the
    compiler's multiword `stores` lowering and the source flat-memory model. -/
set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_store_load_two_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord address left right : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hzeroAdd : 0 + bytesInWord = bytesInWord)
    (haddZero : ∀ value : α, value + 0 = value) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 120 state
        (compileProg context
          (.seq
            (.store (.const address)
              (.rStruct [.const left, .const right]))
            (.return (.load (.comb [.one, .one]) (.const address))))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun current =>
          (state.memory current).map PanValue.word)
        (.seq
          (.store (.const address)
            (.rStruct [.const left, .const right]))
        (.return (.load (.comb [.one, .one]) (.const address))))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hcompile : compileExp context
      (.rStruct [.const left, .const right]) =
      ([.const left, .const right], .comb [.one, .one]) := by
    simp [compileExp, compileExp.compileExpList]
  have hsize : (Shape.comb [.one, .one]).shapeSize = 2 := by
    simp [Shape.shapeSize]
  have hrange : List.range 2 = [0, 1] := by rfl
  have hnames : freshNames context 2 2 =
      [context.maxVar + 2, context.maxVar + 3] := by
    simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
  by_cases hzero : bytesInWord == 0
  · have hbytesZero : bytesInWord = 0 := by simpa using hzero
    by_cases haddr : address == address + bytesInWord
    · simp [Option.bind, compileProg, hcompile, hsize, hrange, hbytesInWord,
        hzeroAdd, haddZero, hzero, hbytesZero, haddr, hnames, compileExp,
    Function.comp_def, freshNames,
    nestedDecs, crepNestedSeq, stores, loadShape, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    restoreCrepResult, evalPanValueProg,
    evalPanValueProgWithPrimitive, evalPanValueExp,
    evalPanValueExp.evalPanValueExps, panValueFlatLoad,
    panValueFlatLoadListFuel, panValueFlatLoadFuel,
    panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
    panValueFlatContextFuel, panValueFlatValueFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel,
    panValueFlatWordsFuel.panValueFlatWordsListFuel,
    panValueFlatOffset, shapeSizeWithContext, evalPanBinOp,
    panValueFlatReadWord, panValueFlatStoreWords,
    panValueStoreWithAccess, updateCrepLocal, updateMemory,
    updatePanValueMemory, updatePanValueMap, isWfShape,
    isWfShape.isWfShapeList,
        panValueFlatWords, panValueFlatWordsFuel]
    · simp [Option.bind, compileProg, hcompile, hsize, hrange, hbytesInWord,
        hzeroAdd, haddZero, hzero, hbytesZero, haddr, hnames, compileExp,
        nestedDecs, crepNestedSeq, stores, loadShape, evalCrepFullResult,
        evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
        restoreCrepResult, evalPanValueProg,
        evalPanValueProgWithPrimitive, evalPanValueExp,
        evalPanValueExp.evalPanValueExps, panValueFlatLoad,
        panValueFlatLoadListFuel, panValueFlatLoadFuel,
        panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
        panValueFlatContextFuel, panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatOffset, shapeSizeWithContext, evalPanBinOp,
        panValueFlatReadWord, panValueFlatStoreWords,
        panValueStoreWithAccess, updateCrepLocal, updateMemory,
        updatePanValueMemory, updatePanValueMap, isWfShape,
        isWfShape.isWfShapeList,
        panValueFlatWords, panValueFlatWordsFuel]
  · by_cases haddr : address == address + bytesInWord
    · simp [Option.bind, compileProg, hcompile, hsize, hrange, hbytesInWord,
        hzeroAdd, haddZero, hzero, haddr, hnames, compileExp,
        nestedDecs, crepNestedSeq, stores, loadShape, evalCrepFullResult,
      evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
      restoreCrepResult, evalPanValueProg,
      evalPanValueProgWithPrimitive, evalPanValueExp,
      evalPanValueExp.evalPanValueExps, panValueFlatLoad,
      panValueFlatLoadListFuel, panValueFlatLoadFuel,
      panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
      panValueFlatContextFuel, panValueFlatValueFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatOffset, shapeSizeWithContext, evalPanBinOp,
      panValueFlatReadWord, panValueFlatStoreWords,
      panValueStoreWithAccess, updateCrepLocal, updateMemory,
      updatePanValueMemory, updatePanValueMap, isWfShape,
      isWfShape.isWfShapeList,
        panValueFlatWords, panValueFlatWordsFuel]
    · simp [Option.bind, compileProg, hcompile, hsize, hrange, hbytesInWord,
        hzeroAdd, haddZero, hzero, haddr, hnames, compileExp,
        nestedDecs, crepNestedSeq, stores, loadShape, evalCrepFullResult,
        evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
        restoreCrepResult, evalPanValueProg,
        evalPanValueProgWithPrimitive, evalPanValueExp,
        evalPanValueExp.evalPanValueExps, panValueFlatLoad,
        panValueFlatLoadListFuel, panValueFlatLoadFuel,
        panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
        panValueFlatContextFuel, panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatOffset, shapeSizeWithContext, evalPanBinOp,
        panValueFlatReadWord, panValueFlatStoreWords,
        panValueStoreWithAccess, updateCrepLocal, updateMemory,
        updatePanValueMemory, updatePanValueMap, isWfShape,
        isWfShape.isWfShapeList,
        panValueFlatWords, panValueFlatWordsFuel]

/-! The fixed-width store32/load32 pair is the direct word-memory case of the
    Pancake correctness induction. -/
theorem compile_full_pan_value_store32_load32_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord address value : α) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 20 state
        (compileProg context
          (.seq
            (.store32 (.const address) (.const value))
            (.return (.load32 (.const address))))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun current =>
          (state.memory current).map PanValue.word)
        (.seq
          (.store32 (.const address) (.const value))
          (.return (.load32 (.const address))))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [Option.bind, compileProg, compileExp, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanValueProg, evalPanValueProgWithPrimitive, evalPanValueExp,
    updateMemory,
    updatePanValueMemory, updatePanValueMap, panValueFlatWords,
    panValueFlatWordsFuel]

/-! The byte-width memory operation has the same source/Crep word
    correspondence for the abstract word-memory model. -/
theorem compile_full_pan_value_storeByte_loadByte_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord address value : α) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 20 state
        (compileProg context
          (.seq
            (.storeByte (.const address) (.const value))
            (.return (.loadByte (.const address))))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals (fun current =>
          (state.memory current).map PanValue.word)
        (.seq
          (.storeByte (.const address) (.const value))
          (.return (.loadByte (.const address))))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  simp [Option.bind, compileProg, compileExp, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanValueProg, evalPanValueProgWithPrimitive, evalPanValueExp,
    updateMemory, updatePanValueMemory, updatePanValueMap,
    panValueFlatWords, panValueFlatWordsFuel]

/-! A zero-condition loop is the first loop-shaped source-to-Crep
    correctness case.  Its body is deliberately arbitrary: neither
    evaluator enters it, so the state and normal-result boundary are
    preserved without imposing a body invariant. -/
theorem compile_full_pan_value_while_zero_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (body : Prog α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.while (.const 0) body)) =
      (evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        structs [] baseAddress topAddress bytesInWord (fuel + 1)
        locals globals sourceMemory (.while (.const 0) body)).map
        (fun result => match result with
        | .normal _ _ _ => []
        | .returned _ _ _ values => values.flatMap panValueFlatWords
        | .raised _ _ _ _ _ => []
        | .broke _ _ _ | .continued _ _ _ => []) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExp, evalPanValueProgWithPrimitiveCallsAndFfi,
    evalPanValueExp]

/-! Loop-control transfers are observable at the full result boundary as
    non-returning outcomes.  The source and Crep evaluators agree on that
    projection for `break`, independently of the surrounding state. -/
theorem compile_full_pan_value_break_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.break : Prog α)) =
      (evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        structs [] baseAddress topAddress bytesInWord (fuel + 1)
        locals globals sourceMemory (.break : Prog α)).bind
        (fun result => match result with
        | .normal _ _ _ => some []
        | .returned _ _ _ values => some (values.flatMap panValueFlatWords)
        | .raised _ _ _ _ _ | .broke _ _ _ | .continued _ _ _ => none) := by
  simp [compileProg, evalCrepFullResult, evalCrepFullProg,
    evalPanValueProgWithPrimitiveCallsAndFfi]

/-! The analogous `continue` transfer also agrees at the result boundary;
    its loop-label representation is erased by the full result projection. -/
theorem compile_full_pan_value_continue_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.continue : Prog α)) =
      (evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        structs [] baseAddress topAddress bytesInWord (fuel + 1)
        locals globals sourceMemory (.continue : Prog α)).bind
        (fun result => match result with
        | .normal _ _ _ => some []
        | .returned _ _ _ values => some (values.flatMap panValueFlatWords)
        | .raised _ _ _ _ _ | .broke _ _ _ | .continued _ _ _ => none) := by
  simp [compileProg, evalCrepFullResult, evalCrepFullProg,
    evalPanValueProgWithPrimitiveCallsAndFfi]

/-! Nonzero loop execution is the main induction interface for the full
    Pancake correctness theorem.  The caller supplies the condition/value
    agreement, the normal body simulation, and the recursive loop result;
    this lemma only performs the outer evaluator step. -/
theorem compile_full_pan_value_while_nonzero_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.normal nextState))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel nextState
      (.while compiledCondition compiledBody) = some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceNonzero, hsourceBody, hsourceLoop]
  · simp [compileProg, hcompileCondition, hcompileBody,
      evalCrepFullProg, hcrepCondition, hconditionAgreement,
      hsourceNonzero, hcrepBody, hcrepLoop]

/-! A nonzero loop whose body breaks consumes the break in both semantics and
    returns normally with the post-body state. -/
theorem compile_full_pan_value_while_break_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.broke sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.broke nextState 0)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) =
      some (.normal nextState) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceNonzero, hsourceBody]
  · simp [compileProg, hcompileCondition, hcompileBody,
      evalCrepFullProg, hcrepCondition, hconditionAgreement,
      hsourceNonzero, hcrepBody]

/-! A nonzero loop whose body continues re-enters the same loop.  This is the
    companion composition rule to the normal-body theorem above. -/
theorem compile_full_pan_value_while_continue_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.continued sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.continued nextState 0))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel nextState
      (.while compiledCondition compiledBody) = some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceNonzero, hsourceBody, hsourceLoop]
  · simp [compileProg, hcompileCondition, hcompileBody,
      evalCrepFullProg, hcrepCondition, hconditionAgreement,
      hsourceNonzero, hcrepBody, hcrepLoop]

/-! Structured sequence composition threads the complete source state and
    control result.  This normal-first rule is the principal constructor
    case for lifting local Pancake simulations to larger programs. -/
theorem compile_full_pan_value_seq_normal_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.normal sourceFirstLocals sourceFirstGlobals sourceFirstMemory))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.normal firstState))
    (hsourceSecond : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceFirstLocals sourceFirstGlobals sourceFirstMemory second =
      some sourceResult)
    (hcrepSecond : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) firstState compiledSecond =
      some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst,
      hsourceSecond]
  · simp [compileProg, hcompileFirst, hcompileSecond,
      evalCrepFullProg, hcrepFirst, hcrepSecond]

/-! A returned first component short-circuits a structured sequence. -/
theorem compile_full_pan_value_seq_return_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceValues : List (PanValue α)) (crepValues : List α)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.returned sourceFirstLocals sourceFirstGlobals sourceFirstMemory
        sourceValues))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.returned firstState crepValues)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some (.returned sourceFirstLocals sourceFirstGlobals sourceFirstMemory
        sourceValues) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some (.returned firstState crepValues) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
  · simp [compileProg, hcompileFirst, hcompileSecond,
      evalCrepFullProg, hcrepFirst]

/-! Non-normal first components also short-circuit structured sequences. -/
theorem compile_full_pan_value_seq_raise_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (crepException : α)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.raised sourceFirstLocals sourceFirstGlobals sourceFirstMemory
        sourceException sourceValue))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.raised firstState crepException)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some (.raised sourceFirstLocals sourceFirstGlobals sourceFirstMemory
        sourceException sourceValue) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some (.raised firstState crepException) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
  · simp [compileProg, hcompileFirst, hcompileSecond,
      evalCrepFullProg, hcrepFirst]

theorem compile_full_pan_value_seq_break_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.broke sourceFirstLocals sourceFirstGlobals sourceFirstMemory))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.broke firstState 0)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some (.broke sourceFirstLocals sourceFirstGlobals sourceFirstMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some (.broke firstState 0) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
  · simp [compileProg, hcompileFirst, hcompileSecond,
      evalCrepFullProg, hcrepFirst]

theorem compile_full_pan_value_seq_continue_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.continued sourceFirstLocals sourceFirstGlobals sourceFirstMemory))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.continued firstState 0)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some (.continued sourceFirstLocals sourceFirstGlobals sourceFirstMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some (.continued firstState 0) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
  · simp [compileProg, hcompileFirst, hcompileSecond,
      evalCrepFullProg, hcrepFirst]

/-! Shared-memory loads are word assignments in Pancake and dispatch through
    the corresponding Crep shared-memory handler operation. -/
theorem compile_full_pan_value_shMemLoad_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state targetState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (size : OpSize) (name : VarName) (slot : Nat) (address value oldValue : α)
    (sourceAddress : Exp α) (compiledAddress : CrepExp α)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (haddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceAddress = some (.word address))
    (hmemory : sourceMemory address = some (.word value))
    (hcompiledAddress : firstCompiledExp context sourceAddress = some compiledAddress)
    (hcrepAddress : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledAddress = some address)
    (hsharedMem : sharedMem (loadMemOp size) slot address state = some targetState)
    (hlocals : sourceLocals name = some (.word oldValue)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.shMemLoad size .local name sourceAddress) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context
        (.shMemLoad size .local name sourceAddress)) =
      some (.normal targetState) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hmemory,
      panValueSharedLoadValid, panValueAssignmentValid, panValueShape,
      panShapeMatches, hlocals]
  · simp [compileProg, lookup, hcompiledAddress, evalCrepFullProg,
      hcrepAddress, hsharedMem]

theorem compile_full_pan_value_shMemStore_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state targetState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (size : OpSize) (address value : α) (sourceAddress sourceValue : Exp α)
    (compiledAddress compiledValue : CrepExp α)
    (haddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceAddress = some (.word address))
    (hvalue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceValue = some (.word value))
    (hcompiledAddress : firstCompiledExp context sourceAddress = some compiledAddress)
    (hcompiledValue : firstCompiledExp context sourceValue = some compiledValue)
    (hcrepAddress : evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) value) state.memory
      baseAddress topAddress compiledAddress = some address)
    (hcrepValue : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledValue = some value)
    (hsharedMem : sharedMem (storeMemOp size) (context.maxVar + 1) address
      { state with
        locals := updateCrepLocal state.locals (context.maxVar + 1) value } =
      some targetState) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory
      (.shMemStore size sourceAddress sourceValue) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory address (.word value))) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.shMemStore size sourceAddress sourceValue)) =
      some (.normal
        { targetState with
          locals := restoreCrepLocal targetState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue,
      updatePanValueMemory]
  · simp [compileProg, hcompiledAddress, hcompiledValue, nestedDecs,
      evalCrepFullProg, hcrepAddress, hcrepValue,
      hsharedMem, restoreCrepResult]

/-! A closed word raise exercises the exception-code lookup and the compiler's
    global payload spill before the Crep exception result is produced. -/
theorem compile_full_pan_value_raise_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord value : α)
    (exception : ExceptionId) (exceptionCode : α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 3
      sourceLocals sourceGlobals sourceMemory
      (.raise exception (.const value)) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.word value)) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 10 state
      (compileProg context (.raise exception (.const value))) =
      some (.raised
        { state with memory := updateMemory state.memory 0 value }
        exceptionCode) := by
  constructor
  · have hlimit : panValuePayloadWithinLimit structs (.word value) = true := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel]
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp, hlimit]
  · have hrestore : restoreCrepLocal
        (updateCrepLocal state.locals (context.maxVar + 1) value)
        (context.maxVar + 1) (state.locals (context.maxVar + 1)) =
        state.locals := by
      funext current
      by_cases hcurrent : current = context.maxVar + 1 <;>
        simp [restoreCrepLocal, updateCrepLocal, hcurrent]
    simp [compileProg, compileExp, hlookup, freshNames, nestedDecs,
      crepNestedSeq, storeGlobals, evalCrepFullProg,
      evalCrepFullExp, updateCrepLocal, restoreCrepResult,
      hrestore]

/-! Structured raise payloads are spilled in source order before the target
    raises.  This two-word case is the first nontrivial instance of that
    general payload relation. -/
theorem compile_full_pan_value_raise_two_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 5
      sourceLocals sourceGlobals sourceMemory
      (.raise exception (.rStruct [.const left, .const right])) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct [.word left, .word right])) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 15 state
      (compileProg context
        (.raise exception (.rStruct [.const left, .const right]))) =
      some (.raised
        { state with
          memory := updateMemory
            (updateMemory state.memory 0 left)
            (0 + bytesInWord) right }
        exceptionCode) := by
  constructor
  · have hlimit : panValuePayloadWithinLimit structs
        (.rStruct [.word left, .word right]) = true := by
      exact panValuePayloadWithinLimit_rStruct_two_words structs left right
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
      evalPanValueExp.evalPanValueExps, hlimit]
  · have hcompile : compileExp context
        (.rStruct [.const left, .const right]) =
        ([.const left, .const right], .comb [.one, .one]) := by
      simp [compileExp, compileExp.compileExpList]
    have hnames : freshNames context 2 1 =
        [context.maxVar + 1, context.maxVar + 2] := by
      simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
    have hprogram : compileProg context
          (.raise exception (.rStruct [.const left, .const right])) =
        (.seq
          (nestedDecs [context.maxVar + 1, context.maxVar + 2]
            [.const left, .const right]
            (crepNestedSeq
              (storeGlobals 0 context.bytesInWord
                [.var (context.maxVar + 1), .var (context.maxVar + 2)])))
          (.raise exceptionCode)) := by
      simp only [compileProg, hcompile, Shape.shapeSize,
        List.length_cons, List.length_nil]
      rw [hnames]
      simp [hlookup]
    rw [hprogram]
    have hrestore : restoreCrepLocal
        (restoreCrepLocal
          (updateCrepLocal
            (updateCrepLocal state.locals (context.maxVar + 1) left)
            (context.maxVar + 2) right)
          (context.maxVar + 2) (state.locals (context.maxVar + 2)))
        (context.maxVar + 1) (state.locals (context.maxVar + 1)) =
        state.locals := by
      funext current
      by_cases hsecond : current = context.maxVar + 2
      · simp [restoreCrepLocal, hsecond]
      · by_cases hfirst : current = context.maxVar + 1 <;>
          simp [restoreCrepLocal, updateCrepLocal, hsecond, hfirst]
    simp [nestedDecs,
      crepNestedSeq, storeGlobals, evalCrepFullProg,
      evalCrepFullExp, updateCrepLocal, restoreCrepResult,
      hrestore, hbytesInWord]

/-! A declaration-level call regression exercises the declaration environment,
    `compileToCrepe`, callee lookup, and flattened Crep return values in one
    compiler-to-Crep correctness statement. -/
def correctnessIdentityDeclarations (value : α) : List (Decl α) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id" [.const value]
        (.return (.var .local "result")), returnShape := .one }]

def correctnessIdentityContext [OfNat α 1] : CompileContext α :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

theorem compile_full_pan_value_identity_declaration_call_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    (evalCrepFullCall
      (compileToCrepe (correctnessIdentityContext (α := α))
        (correctnessIdentityDeclarations value))
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 100
      { locals := fun _ => none, memory := fun _ => none }
      none "main" [] =
      some (.returned
        { locals := fun _ => none, memory := fun _ => none } [value])) := by
  simp [correctnessIdentityContext, correctnessIdentityDeclarations,
      compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
      functionInfos, compileProg, compileExp, compileArgs, allocatedNames,
      nestedDecs, evalCrepFullCall, evalCrepFullProg,
      evalCrepFullExps, evalCrepFullExp, updateCrepLocal, restoreCrepResult,
      lookupCompiledFunction, assignCrepValues, lookupInfo, List.map,
      List.zip, List.foldl]

/-! A generic call constructor for the full correctness induction.  The
    source and Crep callee simulations are supplied as witnesses; this rule
    accounts for the surrounding evaluator step and the compiler's argument
    lowering. -/
theorem compile_full_pan_value_call_state_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α))
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcompileProg : compileProg context (.call info function arguments) =
      .call compiledInfo function (compileArgs context arguments))
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory info function arguments =
      some sourceResult)
    (hcrepCall : evalCrepFullCallState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledInfo function compiledArguments =
      some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.call info function arguments) = some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.call info function arguments)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCall]
  · rw [hcompileProg, hcompileArgs]
    simp [evalCrepFullProgState, hcrepCall]

theorem compile_full_pan_value_call_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α))
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcompileProg : compileProg context (.call info function arguments) =
      .call compiledInfo function (compileArgs context arguments))
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory info function arguments =
      some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledInfo function compiledArguments =
      some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.call info function arguments) = some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.call info function arguments)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCall]
  · rw [hcompileProg, hcompileArgs]
    simp [evalCrepFullProg, hcrepCall]

/-! The source-side declaration-call constructor threads the callee's returned
    globals and memory into the declaration body, then restores the caller's
    declaration local.  This is the induction rule used before relating the
    body to its lowered Crep continuation. -/
theorem evalPanValueProg_decCall_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (value : PanValue α)
    (sourceResult : PanValueControlResult α)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) calleeGlobals calleeMemory [value]))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord fuel
      (updatePanValueMap sourceLocals name value) calleeGlobals calleeMemory body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall, hshape, hbody]

/-! The corresponding Crep rule composes a normal lowered call with its
    continuation body.  Fresh declaration slots are handled by the compiler
    expansion lemma separately, so this rule can be reused for any call
    lowering that has already established the call-state witness. -/
theorem evalCrepFullProg_call_seq_normal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state callState : CrepState α)
    (info : Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (CrepExp α))
    (body : CrepProg α) (result : CrepControlResult α)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress fuel state info function arguments =
      some (.normal callState))
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) callState body = some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (.seq (.call info function arguments) body) = some result := by
  simp [evalCrepFullProg, hcall, hbody]

/-! The one-word declaration-call lowering combines fresh-slot setup, the
    destination-aware call, and the compiled continuation.  Its fuel offsets
    are explicit so later source-to-Crep induction can instantiate this rule
    without unfolding the evaluator by hand. -/
theorem compile_full_pan_value_decCall_one_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state callState : CrepState α) (result : CrepControlResult α)
    (name : VarName) (function : FunName) (arguments : List (Exp α))
    (body : Prog α) (compiledArguments : List (CrepExp α))
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with
          locals := updateCrepLocal state.locals (context.maxVar + 1) 0 }
      (some ([context.maxVar + 1], none)) function compiledArguments =
      some (.normal callState))
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) callState
      (compileProg
        { context with
            vars := (name, (.one, [context.maxVar + 1])) :: context.vars
            maxVar := context.maxVar + 1 }
        body) = some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 3) state
      (compileProg context (.decCall name .one function arguments body)) =
      some (restoreCrepResult (context.maxVar + 1)
        (state.locals (context.maxVar + 1)) result) := by
  simp [compileProg, allocatedNames, nestedDecs,
    evalCrepFullProg, evalCrepFullExp, hcompileArgs, hcall, hbody]

/-! These helpers expose the state transformation performed by a list of
    compiler-generated zero declarations.  The recursive order mirrors
    `nestedDecs`, which makes the multi-word declaration-call proof independent
    of the particular shape being flattened. -/
def initializeCrepLocals {α : Type u} [OfNat α 0]
    (locals : Nat → Option α) : List Nat → Nat → Option α
  | [], current => locals current
  | name :: names, current =>
      initializeCrepLocals (updateCrepLocal locals name 0) names current

def restoreCrepResultList {α : Type u} [OfNat α 0]
    (locals : Nat → Option α) : List Nat →
    CrepControlResult α → CrepControlResult α
  | [], result => result
  | name :: names, result =>
      restoreCrepResult name (locals name)
        (restoreCrepResultList (updateCrepLocal locals name 0) names result)

theorem evalCrepFullProg_nestedDecs_const_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat) (body : CrepProg α)
    (result : CrepControlResult α)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := initializeCrepLocals state.locals names } body =
      some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names (names.map (fun _ => .const 0)) body) =
      some (restoreCrepResultList state.locals names result) := by
  induction names generalizing state result with
  | nil =>
      simpa [nestedDecs, initializeCrepLocals, restoreCrepResultList] using hbody
  | cons name names ih =>
      have hbody' : evalCrepFullProg functions primitive ffi sharedMem
          baseAddress topAddress fuel
          { state with
              locals := initializeCrepLocals
                (updateCrepLocal state.locals name 0) names } body =
          some result := by
        simpa [initializeCrepLocals] using hbody
      have htail := ih
        (state := { state with
          locals := updateCrepLocal state.locals name 0 })
        (result := result) hbody'
      change evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress ((fuel + names.length) + 1) state
        (.dec name (.const 0)
          (nestedDecs names (names.map (fun _ => .const 0)) body)) =
        some (restoreCrepResult name (state.locals name)
          (restoreCrepResultList (updateCrepLocal state.locals name 0)
            names result))
      simp [evalCrepFullProg, evalCrepFullExp, htail]

theorem evalCrepFullProgState_nestedDecs_const_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat) (body : CrepProg α)
    (result : CrepControlResult α)
    (hbody : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := initializeCrepLocals state.locals names } body =
      some result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names (names.map (fun _ => .const 0)) body) =
      some (restoreCrepResultList state.locals names result) := by
  induction names generalizing state result with
  | nil =>
      simpa [nestedDecs, initializeCrepLocals, restoreCrepResultList] using hbody
  | cons name names ih =>
      have hbody' : evalCrepFullProgState functions primitive ffi sharedMem
          baseAddress topAddress fuel
          { state with
              locals := initializeCrepLocals
                (updateCrepLocal state.locals name 0) names } body =
          some result := by
        simpa [initializeCrepLocals] using hbody
      have htail := ih
        (state := { state with
          locals := updateCrepLocal state.locals name 0 })
        (result := result) hbody'
      change evalCrepFullProgState functions primitive ffi sharedMem
        baseAddress topAddress ((fuel + names.length) + 1) state
        (.dec name (.const 0)
          (nestedDecs names (names.map (fun _ => .const 0)) body)) =
        some (restoreCrepResult name (state.locals name)
          (restoreCrepResultList (updateCrepLocal state.locals name 0)
            names result))
      simp [evalCrepFullProgState, evalCrepFullExpState, htail]

/-! With the generic nested-declaration rule, the destination-aware lowering
    of `decCall` composes for every flattened result shape. -/
theorem compile_full_pan_value_decCall_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state callState : CrepState α) (result : CrepControlResult α)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal callState))
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) callState
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress
      (fuel + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) result) := by
  have hseq : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2)
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (.seq
        (.call (some (allocatedNames context shape, none)) function compiledArguments)
        (compileProg
          { context with
              vars := (name, (shape, allocatedNames context shape)) :: context.vars
              maxVar := context.maxVar + Shape.shapeSize shape }
          body)) = some result := by
    simp [evalCrepFullProg, hcall, hbody]
  have hnested := evalCrepFullProg_nestedDecs_const_zero
    functions primitive ffi sharedMem baseAddress topAddress (fuel + 2) state
    (allocatedNames context shape)
    (.seq
      (.call (some (allocatedNames context shape, none)) function compiledArguments)
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body)) result hseq
  simpa [compileProg, allocatedNames, nestedDecs, hcompileArgs, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hnested

theorem compile_full_pan_value_decCall_state_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state callState : CrepState α) (result : CrepControlResult α)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcall : evalCrepFullCallState functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal callState))
    (hbody : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) callState
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (fuel + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) result) := by
  have hseq : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2)
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (.seq
        (.call (some (allocatedNames context shape, none)) function compiledArguments)
        (compileProg
          { context with
              vars := (name, (shape, allocatedNames context shape)) :: context.vars
              maxVar := context.maxVar + Shape.shapeSize shape }
          body)) = some result := by
    simp [evalCrepFullProgState, hcall, hbody]
  have hnested := evalCrepFullProgState_nestedDecs_const_zero
    functions primitive ffi sharedMem baseAddress topAddress (fuel + 2) state
    (allocatedNames context shape)
    (.seq
      (.call (some (allocatedNames context shape, none)) function compiledArguments)
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body)) result hseq
  simpa [compileProg, allocatedNames, nestedDecs, hcompileArgs, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hnested

/-! A normal callee return is the target-side witness needed by `decCall`:
    returned words are assigned to the caller's destination slots and the
    callee's memory is retained. -/
theorem evalCrepFullCall_returned_with_destinations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (destinations : List Nat) (arguments : List (CrepExp α))
    (values : List α) (parameters : List Nat) (body : CrepProg α)
    (calleeLocals : Nat → Option α) (callee : CrepState α)
    (calleeValues : List α) (callerLocals : Nat → Option α)
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments = some values)
    (hlookup : lookupCompiledFunction function functions = some (parameters, body))
    (hassign : assignCrepValues (fun _ => none) parameters values =
      some calleeLocals)
    (hcallee : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := calleeLocals, memory := caller.memory } body =
      some (.returned callee calleeValues))
    (hdestinations : assignCrepValues caller.locals destinations calleeValues =
      some callerLocals) :
    evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (some (destinations, none)) function arguments =
      some (.normal { locals := callerLocals, memory := callee.memory }) := by
  simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee, hdestinations]

/-! The source-side normal-return call rule makes the validation and parameter
    binding obligations explicit.  The no-destination form is the callee
    witness consumed by `decCall`. -/
theorem evalPanValueCall_returned_no_destination
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (body : Prog α) (calleeLocals : VarName → Option (PanValue α))
    (calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α))
    (calleeBodyLocals : VarName → Option (PanValue α))
    (calleeValues : List (PanValue α))
    (hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hcallee : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord fuel
      calleeLocals sourceGlobals sourceMemory body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned calleeBodyLocals calleeGlobals calleeMemory calleeValues))
    (hreturn : panValueReturnValid structs contracts function calleeValues = true)
    (hlimit : panValueValuesWithinLimit structs calleeValues = true) :
    evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) calleeGlobals calleeMemory calleeValues) := by
  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
    hparameters, hbind, hcallee, hreturn, hlimit]

/-! Couple the source and target declaration-call constructors.  The theorem
    deliberately keeps the source and Crep body simulations as hypotheses:
    those are supplied by the main induction and this rule only accounts for
    the call boundary, fresh slots, and continuation bookkeeping. -/
theorem compile_full_pan_value_decCall_compose_full
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state callState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hsourceShape : panShapeMatches
      (panValueShape structs sourceValue) shape = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal callState))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) callState
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (fuel + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  constructor
  · apply evalPanValueProg_decCall_compose
    · exact hsourceCall
    · exact hsourceShape
    · exact hsourceBody
  · apply compile_full_pan_value_decCall_compose
    · exact hcompileArgs
    · exact hcrepCall
    · exact hcrepBody

/-! Expose the exact compiler equation for declaration calls.  Keeping this
    expansion named prevents later correctness proofs from duplicating the
    fresh-slot and continuation-context bookkeeping. -/
theorem compileProg_decCall_expansion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α) :
    compileProg context (.decCall name shape function arguments body) =
      nestedDecs (allocatedNames context shape)
        ((allocatedNames context shape).map (fun _ => .const 0))
        (.seq
          (.call (some (allocatedNames context shape, none)) function
            (compileArgs context arguments))
          (compileProg
            { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize shape }
            body)) := by
  simp [compileProg]

end Flapjack
