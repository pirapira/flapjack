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
    exact hwordsFuel (values.length + 1) values (by omega)
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
          (panValueFlatValueFuel
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
          (panValueFlatValueFuel
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

end Flapjack
