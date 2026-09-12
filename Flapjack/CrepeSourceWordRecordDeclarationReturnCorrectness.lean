import Flapjack.CrepeSourceWordRecordRaiseCorrectness

/-!
Scoped structured declaration followed by a return of the declared value.

This is the first declaration case whose result crosses the source/Crep
boundary: Pancake returns one structured value, while Crep returns its two
flattened words after restoring the declaration temporaries.
-/

namespace Flapjack

theorem compile_full_pan_value_dec_two_word_record_return_relation
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
    (hempty : sourceLocals = (fun _ => none))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs [] baseAddress topAddress bytesInWord 10
      sourceLocals sourceGlobals sourceMemory
      (.dec name (.comb [.one, .one])
        (.rStruct [.const left, .const right])
        (.return (.var .local name))) =
      some (.returned sourceLocals sourceGlobals sourceMemory
        [.rStruct [.word left, .word right]]) ∧
    evalCrepFullProg [] crepPrimitive ffi sharedMem baseAddress topAddress 10 state
      (compileProg context
        (.dec name (.comb [.one, .one])
          (.rStruct [.const left, .const right])
          (.return (.var .local name)))) =
      some (.returned state [left, right]) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.returned sourceLocals sourceGlobals sourceMemory
        [.rStruct [.word left, .word right]])
      (.returned state [left, right]) := by
  have hsource : evalPanValueExp structs sourceLocals sourceGlobals
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
  have hvar : evalPanValueExp structs
      (updatePanValueMap sourceLocals name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) =
      some (.rStruct [.word left, .word right]) := by
    simp [evalPanValueExp, updatePanValueMap]
  have hrestoreSourceEmpty : restorePanValueLocal
      (fun _ : VarName => (none : Option (PanValue α))) name none =
      (fun _ : VarName => (none : Option (PanValue α))) := by
    funext current
    by_cases hcurrent : current == name <;>
      simp [restorePanValueLocal, hcurrent]
  have hsourceEmpty : evalPanValueExp structs
      (fun _ => none) sourceGlobals sourceMemory baseAddress topAddress bytesInWord
      (.rStruct [.const left, .const right]) =
      some (.rStruct [.word left, .word right]) := by
    simpa [hempty] using hsource
  have hvarEmpty : evalPanValueExp structs
      (updatePanValueMap (fun _ => none) name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) =
      some (.rStruct [.word left, .word right]) := by
    simpa [hempty] using hvar
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi,
      hsourceEmpty, hshape, restorePanValueControlLocal,
      hrestoreSourceEmpty, hvarEmpty, hempty]
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
            (.rStruct [.const left, .const right])
            (.return (.var .local name))) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [.const left, .const right]
          (.return [.var (context.maxVar + 1), .var (context.maxVar + 2)]) := by
      simp only [compileProg, hcompile]
      rw [hnames]
      simp [compileExp, lookupInfo]
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
      evalCrepFullExps, updateCrepLocal, restoreCrepResult, hrestore]
  · refine ⟨hrel, ?_⟩
    simp [panValueCrepValuesRel, panValueFlatWords, panValueFlatWordsFuel,
      panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel]

end Flapjack

namespace Flapjack

/-!
Stateful counterpart of the structured declaration/return boundary.  The
legacy theorem above is retained as a compatibility alias for callers that
have not migrated to the state-threading evaluator yet.
-/

theorem compile_full_pan_value_dec_two_word_record_return_state_relation
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
    (hempty : sourceLocals = (fun _ => none))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs [] baseAddress topAddress bytesInWord 10
      sourceLocals sourceGlobals sourceMemory
      (.dec name (.comb [.one, .one])
        (.rStruct [.const left, .const right])
        (.return (.var .local name))) =
      some (.returned sourceLocals sourceGlobals sourceMemory
        [.rStruct [.word left, .word right]]) ∧
    evalCrepFullProgState [] crepPrimitive ffi sharedMem baseAddress topAddress 10 state
      (compileProg context
        (.dec name (.comb [.one, .one])
          (.rStruct [.const left, .const right])
          (.return (.var .local name)))) =
      some (.returned state [left, right]) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.returned sourceLocals sourceGlobals sourceMemory
        [.rStruct [.word left, .word right]])
      (.returned state [left, right]) := by
  have hsource : evalPanValueExp structs sourceLocals sourceGlobals
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
  have hvar : evalPanValueExp structs
      (updatePanValueMap sourceLocals name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) =
      some (.rStruct [.word left, .word right]) := by
    simp [evalPanValueExp, updatePanValueMap]
  have hrestoreSourceEmpty : restorePanValueLocal
      (fun _ : VarName => (none : Option (PanValue α))) name none =
      (fun _ => none) := by
    funext current
    by_cases hcurrent : current == name <;>
      simp [restorePanValueLocal, hcurrent]
  have hsourceEmpty : evalPanValueExp structs
      (fun _ => none) sourceGlobals sourceMemory baseAddress topAddress bytesInWord
      (.rStruct [.const left, .const right]) =
      some (.rStruct [.word left, .word right]) := by
    simpa [hempty] using hsource
  have hvarEmpty : evalPanValueExp structs
      (updatePanValueMap (fun _ => none) name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) =
      some (.rStruct [.word left, .word right]) := by
    simpa [hempty] using hvar
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi,
      hsourceEmpty, hshape, restorePanValueControlLocal,
      hrestoreSourceEmpty, hvarEmpty, hempty]
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
            (.rStruct [.const left, .const right])
            (.return (.var .local name))) =
        nestedDecs [context.maxVar + 1, context.maxVar + 2]
          [.const left, .const right]
          (.return [.var (context.maxVar + 1), .var (context.maxVar + 2)]) := by
      simp only [compileProg, hcompile]
      rw [hnames]
      simp [compileExp, lookupInfo]
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
      evalCrepFullExpsState, updateCrepLocal, restoreCrepResult, hrestore]
  · refine ⟨hrel, ?_⟩
    simp [panValueCrepValuesRel, panValueFlatWords, panValueFlatWordsFuel,
      panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel]

end Flapjack
