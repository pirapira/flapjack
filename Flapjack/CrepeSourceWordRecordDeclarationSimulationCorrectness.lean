import Flapjack.CrepeSourceWordRecordDeclarationCorrectness

/-!
Concrete declaration simulation for the empty body case.

This is the first scoped structured declaration case: both evaluators bind the
two-word record, execute `skip`, and restore their pre-declaration state.
-/

namespace Flapjack

theorem compile_full_pan_value_dec_two_word_skip_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (left right : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs [] baseAddress topAddress bytesInWord 10
      sourceLocals sourceGlobals sourceMemory
      (.dec name (.comb [.one, .one])
        (.rStruct [.const left, .const right]) .skip) =
      some (.normal sourceLocals sourceGlobals sourceMemory) ∧
    evalCrepFullProg [] crepPrimitive ffi sharedMem baseAddress topAddress 10 state
      (compileProg context
        (.dec name (.comb [.one, .one])
          (.rStruct [.const left, .const right]) .skip)) =
      some (.normal state) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal state) := by
  constructor
  · have hsource : evalPanValueExp structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (.rStruct [.const left, .const right]) =
        some (.rStruct [.word left, .word right]) := by
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
    have hshape : panShapeMatches
        (panValueShape structs (.rStruct [.word left, .word right]))
        (.comb [.one, .one]) = true := by
      simp [panValueShape, panShapeMatches,
        panShapeMatches.panShapeListMatches]
    have hrestoreSource : restorePanValueLocal
        (updatePanValueMap sourceLocals name
          (.rStruct [.word left, .word right])) name (sourceLocals name) =
        sourceLocals := by
      funext current
      by_cases hcurrent : current == name
      · have heq : current = name := by simpa using hcurrent
        subst current
        simp [restorePanValueLocal]
      · simp [restorePanValueLocal, updatePanValueMap, hcurrent]
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, panValueShape, panShapeMatches,
      panShapeMatches.panShapeListMatches, restorePanValueControlLocal,
      hsource, hrestoreSource]
  constructor
  · have hcompile : compileExp context
        (.rStruct [.const left, .const right]) =
        ([.const left, .const right], .comb [.one, .one]) := by
      simp [compileExp, compileExp.compileExpList]
    have hnames : allocatedNames context (.comb [.one, .one]) =
        [context.maxVar + 1, context.maxVar + 2] := by
      simp [allocatedNames, Shape.shapeSize, List.range, List.range.loop]
    have hprogram : compileProg context
          (.dec name (.comb [.one, .one])
            (.rStruct [.const left, .const right]) .skip) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [.const left, .const right] .skip := by
      simp only [compileProg, hcompile]
      rw [hnames]
      simp
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
    simp [nestedDecs, evalCrepFullProg, evalCrepFullExp,
      updateCrepLocal, restoreCrepResult, hrestore]
  · simpa [panValueCrepControlRel] using hrel

end Flapjack

namespace Flapjack

/-!
Stateful counterpart of the concrete declaration simulation above.  The
compatibility theorem remains available for callers that still use the legacy
evaluator; this boundary explicitly threads `CrepState` through the stateful
evaluator used by the migrated correctness suite.
-/

theorem compile_full_pan_value_dec_two_word_skip_source_word_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (left right : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs [] baseAddress topAddress bytesInWord 10
      sourceLocals sourceGlobals sourceMemory
      (.dec name (.comb [.one, .one])
        (.rStruct [.const left, .const right]) .skip) =
      some (.normal sourceLocals sourceGlobals sourceMemory) ∧
    evalCrepFullProgState [] crepPrimitive ffi sharedMem baseAddress topAddress 10 state
      (compileProg context
        (.dec name (.comb [.one, .one])
          (.rStruct [.const left, .const right]) .skip)) =
      some (.normal state) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal state) := by
  constructor
  · have hsource : evalPanValueExp structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (.rStruct [.const left, .const right]) =
        some (.rStruct [.word left, .word right]) := by
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
    have hshape : panShapeMatches
        (panValueShape structs (.rStruct [.word left, .word right]))
        (.comb [.one, .one]) = true := by
      simp [panValueShape, panShapeMatches,
        panShapeMatches.panShapeListMatches]
    have hrestoreSource : restorePanValueLocal
        (updatePanValueMap sourceLocals name
          (.rStruct [.word left, .word right])) name (sourceLocals name) =
        sourceLocals := by
      funext current
      by_cases hcurrent : current == name
      · have heq : current = name := by simpa using hcurrent
        subst current
        simp [restorePanValueLocal]
      · simp [restorePanValueLocal, updatePanValueMap, hcurrent]
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, panValueShape, panShapeMatches,
      panShapeMatches.panShapeListMatches, restorePanValueControlLocal,
      hsource, hrestoreSource]
  constructor
  · have hcompile : compileExp context
        (.rStruct [.const left, .const right]) =
        ([.const left, .const right], .comb [.one, .one]) := by
      simp [compileExp, compileExp.compileExpList]
    have hnames : allocatedNames context (.comb [.one, .one]) =
        [context.maxVar + 1, context.maxVar + 2] := by
      simp [allocatedNames, Shape.shapeSize, List.range, List.range.loop]
    have hprogram : compileProg context
          (.dec name (.comb [.one, .one])
            (.rStruct [.const left, .const right]) .skip) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [.const left, .const right] .skip := by
      simp only [compileProg, hcompile]
      rw [hnames]
      simp
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
    simp [nestedDecs, evalCrepFullProgState, evalCrepFullExpState,
      updateCrepLocal, restoreCrepResult, hrestore]
  · simpa [panValueCrepControlRel] using hrel

end Flapjack
