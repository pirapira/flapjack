import Flapjack.CrepeSourceWordRecordDeclarationSimulationCorrectness
import Flapjack.CrepeRaiseCorrectness

/-!
Lift the structured two-word exception theorem to source-word fields.

The field expressions may be arbitrary scalar source-word expressions; their
compiled forms and evaluator results are supplied as the usual expression
obligations.  This is the structured raise case of the Pancake correctness
induction.
-/

namespace Flapjack

theorem compile_full_pan_value_raise_source_word_two_fields_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (fieldLeft fieldRight : SourceWordExp α) (left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (compiledLeft compiledRight : CrepExp α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      some (.rStruct [.word left, .word right]))
    (hcompile : compileExp context
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      ([compiledLeft, compiledRight], .comb [.one, .one]))
    (hcompiledLeft : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledLeft = some left)
    (hcompiledRight : ∀ value : α, evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) value)
      state.memory baseAddress topAddress compiledRight = some right)
    (hexception : exceptionRel exception
      (.rStruct [.word left, .word right]) exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 5 sourceLocals sourceGlobals sourceMemory
      (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp])) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right])) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 15 state
      (compileProg context
        (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp]))) =
      some (.raised
        { state with memory :=
            (updateMemory
              (updateMemory state.memory 0 left) (0 + bytesInWord) right) }
        exceptionCode) ∧
    panValueCrepRaisedControlRelExcept structs context exceptionRel sourceGlobals
      sourceMemory exception (.rStruct [.word left, .word right])
      { locals := state.locals
        memory := updateMemory
          (updateMemory state.memory 0 left) (0 + bytesInWord) right }
      exceptionCode (fun address => address = 0 ∨ address = 0 + bytesInWord) := by
  constructor
  · have hvalid : panValuePayloadWithinLimit structs
        (.rStruct [.word left, .word right]) = true := by
      exact panValuePayloadWithinLimit_rStruct_two_words structs left right
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · have hnames : freshNames context 2 1 =
        [context.maxVar + 1, context.maxVar + 2] := by
      simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
    have hprogram : compileProg context
          (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp])) =
        (.seq
          (nestedDecs [context.maxVar + 1, context.maxVar + 2]
            [compiledLeft, compiledRight]
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
    simp [nestedDecs, crepNestedSeq, storeGlobals, evalCrepFullProg,
      evalCrepFullExp, updateCrepLocal, restoreCrepResult, hrestore,
      hcompiledLeft, hcompiledRight, hbytesInWord]
  · have hstate := panValueCrepRaisedStateRel_two_word_spill
      structs context sourceLocals sourceGlobals sourceMemory state
      0 bytesInWord left right hrel
    exact ⟨hstate, hexception⟩

end Flapjack

namespace Flapjack

/-! Stateful/global-aware counterpart of the structured two-word raise case. -/

theorem compile_full_pan_value_raise_source_word_two_fields_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (fieldLeft fieldRight : SourceWordExp α) (left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (compiledLeft compiledRight : CrepExp α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      some (.rStruct [.word left, .word right]))
    (hcompile : compileExp context
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      ([compiledLeft, compiledRight], .comb [.one, .one]))
    (hcompiledLeft : evalCrepFullExpState state baseAddress topAddress compiledLeft =
      some left)
    (hcompiledRight : ∀ value : α, evalCrepFullExpState
      { state with locals := updateCrepLocal state.locals (context.maxVar + 1) value }
      baseAddress topAddress compiledRight = some right)
    (hexception : exceptionRel exception
      (.rStruct [.word left, .word right]) exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 5 sourceLocals sourceGlobals sourceMemory
      (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp])) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right])) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress 15 state
      (compileProg context
        (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp]))) =
      some (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode) ∧
    panValueCrepRaisedControlRelExcept structs context exceptionRel sourceGlobals
      sourceMemory exception (.rStruct [.word left, .word right])
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) }
      exceptionCode (fun address => address = 0 ∨ address = 0 + bytesInWord) := by
  constructor
  · have hvalid : panValuePayloadWithinLimit structs
        (.rStruct [.word left, .word right]) = true := by
      exact panValuePayloadWithinLimit_rStruct_two_words structs left right
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · have hnames : freshNames context 2 1 =
        [context.maxVar + 1, context.maxVar + 2] := by
      simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
    have hprogram : compileProg context
          (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp])) =
        (.seq
          (nestedDecs [context.maxVar + 1, context.maxVar + 2]
            [compiledLeft, compiledRight]
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
    simp [nestedDecs, crepNestedSeq, storeGlobals, evalCrepFullProgState,
      evalCrepFullExpState, updateCrepLocal, restoreCrepResult, hrestore,
      hcompiledLeft, hcompiledRight, hbytesInWord]
  · have hstate := panValueCrepRaisedStateRel_two_word_spill
      structs context sourceLocals sourceGlobals sourceMemory state
      0 bytesInWord left right hrel
    have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
        state.locals := by
      intro name currentValue shape slots hsource _
      simp at hsource
    have hmemory : panValueCrepMemoryRelExcept sourceMemory state.memory
        (fun address => address = 0 ∨ address = 0 + bytesInWord) := by
      intro address _
      exact congrFun hrel.2.2 address
    refine ⟨?_, hexception⟩
    exact ⟨hstate.1, hlocals, hmemory⟩

end Flapjack
