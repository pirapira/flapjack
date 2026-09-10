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

theorem compile_full_skip_correct
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

theorem compile_full_return_const_correct
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

theorem compile_full_add_const_correct
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

theorem compile_full_store_load_const_correct
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

theorem compile_full_ite_const_correct
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

theorem compile_full_extCall_const_noop_correct
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
        | .raised _ _ | .broke _ _ | .continued _ _ => none) = _
  have hsecond' :
      (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress fuel
        firstState (compileProg context second)).bind (fun result =>
          match result with
          | .returned _ values => some values
          | .normal _ => some []
          | .raised _ _ | .broke _ _ | .continued _ _ => none) =
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

end Flapjack
