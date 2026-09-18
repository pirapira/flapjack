import Flapjack.CrepeGlobalStoreCorrectness
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramAssignmentCorrectness
import Flapjack.CrepeAllocationNameLemmas

/-!
Generic structured-value Raise lowering.

This is the evaluator-facing part of the HOL Raise case: arbitrary flattened
values are evaluated into fresh temporaries, written to the compiler-owned
global area, and then raised with the looked-up exception code.  The separate
payload-observation theorem remains responsible for connecting that global
area to `globals_lookup` at the exact `pc_compile_correct` boundary.
-/

namespace Flapjack

theorem evalCrepFullProgState_raise_of_evidence_of_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (compiled : List (CrepExp α)) (shape : Shape)
    (values : List α) (extraFuel : Nat)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2 + extraFuel)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  let temporaries := freshNames context compiled.length 1
  let body := crepNestedSeq
    (storeGlobals 0 context.bytesInWord (temporaries.map (fun name => .var name)))
  let bodyState : CrepState α :=
    { state with locals := updateCrepLocalList state.locals temporaries values }
  let targetState : CrepState α :=
    { state with globals := updateMemoryListAt state.globals 0 context.bytesInWord values }
  have hvaluesLength : compiled.length = values.length :=
    evalCrepFullExpsState_length state baseAddress topAddress compiled values hcompiled
  have htemporaryLength : temporaries.length = values.length := by
    simp [temporaries, freshNames, hvaluesLength]
  have htemporaryDistinct : CrepDistinctNames temporaries := by
    exact crepDistinctNames_freshNames context compiled.length 1
  have hcompiledTemporaries : evalCrepFullExpsState bodyState
      baseAddress topAddress (temporaries.map (fun name => .var name)) =
      some values := by
    exact evalCrepFullExpsState_varList_updateCrepLocalList
      state baseAddress topAddress temporaries values htemporaryLength
      htemporaryDistinct
  have hbody := evalCrepFullProgState_storeGlobals_vars_of_fuel
    functions primitive ffi sharedMem baseAddress topAddress
    (values.length + 1 + extraFuel) bodyState 0 context.bytesInWord
    temporaries values (by omega) htemporaryLength hcompiledTemporaries
  have hbody' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (values.length + 1 + extraFuel) bodyState body =
      some (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) := by
    simpa [body] using hbody
  have hnested : CrepNestedDecsStateEval functions primitive ffi sharedMem
      baseAddress topAddress (values.length + 1 + extraFuel) state temporaries
      compiled body (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) := by
    exact crepNestedDecsStateEval_of_evalExps_stable
      functions primitive ffi sharedMem baseAddress topAddress
      (values.length + 1 + extraFuel) state temporaries compiled body
      (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values })
      values (htemporaryLength.trans hvaluesLength.symm) hnot hcompiled hbody'
  have hnestedEval := evalCrepFullProgState_nestedDecs_of_eval
    functions primitive ffi sharedMem baseAddress topAddress
    (values.length + 1 + extraFuel) state temporaries compiled body
    (.normal { bodyState with
      globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values })
    htemporaryDistinct hnested
  have hrestoreLocals :
      restoredCrepLocals state.locals bodyState.locals temporaries =
        state.locals := by
    exact restoredCrepLocals_updateCrepLocalList state.locals temporaries values
      htemporaryLength htemporaryDistinct (by
        intro name hmem
        exact hfresh name (by simpa [temporaries] using hmem))
  have hnestedEval' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + 1 + extraFuel + temporaries.length) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    have hrestored : restoreCrepResultList state.locals temporaries
        (.normal { bodyState with
          globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) =
        .normal targetState := by
      have hrestored' := restoreCrepResultList_normal_explicit
        state.locals bodyState.locals bodyState.memory temporaries
        (updateMemoryListAt bodyState.globals 0 context.bytesInWord values)
      rw [hrestoreLocals] at hrestored'
      simpa [bodyState, targetState] using hrestored'
    simpa [hrestored] using hnestedEval
  have hcompileProg : compileProg context (.raise exception expression) =
      .seq (nestedDecs temporaries compiled body) (.raise exceptionCode) := by
    simp only [compileProg, hlookup, hcompile, hlength, temporaries, body]
    rfl
  rw [hcompileProg]
  change evalCrepFullProgState functions primitive ffi sharedMem
    baseAddress topAddress
    ((values.length + temporaries.length + 1) + 1 + extraFuel) state
    (.seq (nestedDecs temporaries compiled body) (.raise exceptionCode)) = _
  have hnestedEval'' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + temporaries.length + 1 + extraFuel) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval'
  have hfuel : values.length + temporaries.length + 2 + extraFuel =
      (values.length + temporaries.length + 1 + extraFuel) + 1 := by omega
  rw [hfuel]
  have hsecondFuel : values.length + temporaries.length + 1 + extraFuel =
      (values.length + temporaries.length + extraFuel) + 1 := by omega
  rw [hsecondFuel]
  have hnestedEval''' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + temporaries.length + extraFuel + 1) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval''
  simp [evalCrepFullProgState, hnestedEval''', targetState]

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_raise_state_relation_of_evidence
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
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel : Nat) (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception sourceValue) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode 0 := by
  let temporaries := freshNames context compiled.length 1
  let body := crepNestedSeq
    (storeGlobals 0 context.bytesInWord (temporaries.map (fun name => .var name)))
  let bodyState : CrepState α :=
    { state with locals := updateCrepLocalList state.locals temporaries values }
  let bodyResultState : CrepState α :=
    { bodyState with globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }
  let targetState : CrepState α :=
    { state with globals := updateMemoryListAt state.globals 0 context.bytesInWord values }
  have hvaluesLength : compiled.length = values.length :=
    evalCrepFullExpsState_length state baseAddress topAddress compiled values hcompiled
  have htemporaryLength : temporaries.length = values.length := by
    simp [temporaries, freshNames, hvaluesLength]
  have htemporaryDistinct : CrepDistinctNames temporaries := by
    exact crepDistinctNames_freshNames context compiled.length 1
  have hcompiledTemporaries : evalCrepFullExpsState bodyState
      baseAddress topAddress (temporaries.map (fun name => .var name)) =
      some values := by
    exact evalCrepFullExpsState_varList_updateCrepLocalList
      state baseAddress topAddress temporaries values htemporaryLength
      htemporaryDistinct
  have hbody := evalCrepFullProgState_storeGlobals_vars
    functions crepPrimitive ffi sharedMem baseAddress topAddress bodyState
    0 context.bytesInWord temporaries values htemporaryLength
    hcompiledTemporaries
  have hnested : CrepNestedDecsStateEval functions crepPrimitive ffi sharedMem
      baseAddress topAddress (values.length + 1) state temporaries compiled body
      (.normal bodyResultState) := by
    have hbody' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (values.length + 1) bodyState body =
        some (.normal bodyResultState) := by
      simpa [bodyState, bodyResultState, body] using hbody
    exact crepNestedDecsStateEval_of_evalExps_stable
      functions crepPrimitive ffi sharedMem baseAddress topAddress
      (values.length + 1) state temporaries compiled body (.normal bodyResultState)
      values (htemporaryLength.trans hvaluesLength.symm) hnot hcompiled hbody'
  have hnestedEval := evalCrepFullProgState_nestedDecs_of_eval
    functions crepPrimitive ffi sharedMem baseAddress topAddress
    (values.length + 1) state temporaries compiled body (.normal bodyResultState)
    htemporaryDistinct hnested
  have hrestoreLocals :
      restoredCrepLocals state.locals bodyState.locals temporaries =
        state.locals := by
    exact restoredCrepLocals_updateCrepLocalList state.locals temporaries values
      htemporaryLength htemporaryDistinct (by
        intro name hmem
        exact hfresh name (by simpa [temporaries] using hmem))
  have hrestored : restoreCrepResultList state.locals temporaries
      (.normal bodyResultState) = .normal targetState := by
    have hrestored' := restoreCrepResultList_normal_explicit
      state.locals bodyState.locals bodyState.memory temporaries
      bodyResultState.globals
    rw [hrestoreLocals] at hrestored'
    simpa [bodyResultState, bodyState, targetState] using hrestored'
  have hnestedEval' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + 1 + temporaries.length) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [hrestored] using hnestedEval
  have hcompileProg : compileProg context (.raise exception expression) =
      .seq (nestedDecs temporaries compiled body) (.raise exceptionCode) := by
    simp only [compileProg, hlookup, hcompile, hlength, temporaries, body]
    rfl
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · rw [hcompileProg]
    change evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress ((values.length + temporaries.length + 1) + 1) state
      (.seq (nestedDecs temporaries compiled body) (.raise exceptionCode)) = _
    have hnestedEval'' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (values.length + temporaries.length + 1) state
        (nestedDecs temporaries compiled body) =
        some (.normal targetState) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval'
    simp [evalCrepFullProgState, hnestedEval'', targetState]
  · have hstate : panValueCrepRaisedStateRel structs context
        sourceGlobals sourceMemory targetState 0 := by
      refine ⟨?_, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
      · exact hrel.1
      · intro address _
        exact congrFun hrel.2.2 address
    exact ⟨hstate, hexception⟩

theorem panValueCrepProgramStateCorrect_raise_one_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (value : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct [.word value]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct [.const value])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord (.rStruct [.const value]) =
            some (.rStruct [.word value]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context (.rStruct [.const value]) =
            ([.const value], .comb [.one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs (.rStruct [.word value]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress [.const value] =
            some [value] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength : [(.const value : CrepExp α)].length =
          Shape.shapeSize (.comb [.one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 1 1,
          ∀ expression ∈ ([.const value] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh : ∀ name ∈ freshNames context 1 1,
          state.locals name = none := by
        simpa [freshNames] using hfresh context state
      have hexception' := hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 1 1 =
          [context.maxVar + 1] := by
        simp [freshNames, List.range, List.range.loop]
      have hcompileProg : compileProg context
          (.raise exception (.rStruct [.const value])) =
          .seq
            (nestedDecs [context.maxVar + 1] [.const value]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      rw [hcompileProg] at hcrep
                      have hfreshName : state.locals (context.maxVar + 1) = none := by
                        exact hfresh (context.maxVar + 1) (by
                          rw [hnames]
                          simp)
                      simp [evalCrepFullProgState, evalCrepFullExpState,
                        nestedDecs, crepNestedSeq, storeGlobals, hfreshName,
                        updateCrepLocal, restoreCrepResult] at hcrep
                      have hrestore :
                          restoreCrepLocal
                              (updateCrepLocal state.locals
                                (context.maxVar + 1) value)
                              (context.maxVar + 1) none = state.locals := by
                        funext current
                        by_cases hcurrent : current = context.maxVar + 1
                        · subst current
                          simp [restoreCrepLocal, hfreshName]
                        · simp [restoreCrepLocal, updateCrepLocal, hcurrent]
                      rw [hrestore] at hcrep
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                        hsourceValue, panValuePayloadWithinLimit] at hsource
                      have hsourceEq := hsource.2
                      have hcrepEq := hcrep
                      cases hsourceEq
                      cases hcrepEq
                      have hstate : panValueCrepRaisedStateRel structs context
                          sourceGlobals sourceMemory
                          { state with
                              globals := updateMemory state.globals 0 value } 0 := by
                        refine ⟨hrel.1,
                          panValueCrepLocalsRel_empty structs context state.locals,
                          ?_⟩
                        intro address _
                        exact congrFun hrel.2.2 address
                      exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_two_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (left right : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct [.word left, .word right]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct [.const left, .const right])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const left, .const right]) =
            some (.rStruct [.word left, .word right]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context (.rStruct [.const left, .const right]) =
            ([.const left, .const right], .comb [.one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word left, .word right]) = true := by
        exact panValuePayloadWithinLimit_rStruct_two_words structs left right
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const left, .const right] = some [left, right] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const left : CrepExp α), .const right].length =
            Shape.shapeSize (.comb [.one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 2 1,
          ∀ expression ∈ ([.const left, .const right] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 2 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1 (hfresh context state).2
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 2 1 =
          [context.maxVar + 1, context.maxVar + 2] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception (.rStruct [.const left, .const right])) =
          .seq
            (nestedDecs [context.maxVar + 1, context.maxVar + 2]
              [.const left, .const right]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState, evalCrepFullExpState,
                                updateCrepLocal, restoreCrepResult] at hcrep
                          | succ targetFuel =>
                              rw [hcompileProg] at hcrep
                              have hfreshLeft :
                                  state.locals (context.maxVar + 1) = none := by
                                exact (hfresh context state).1
                              have hfreshRight :
                                  state.locals (context.maxVar + 2) = none := by
                                exact (hfresh context state).2
                              simp [evalCrepFullProgState, evalCrepFullExpState,
                                nestedDecs, crepNestedSeq, storeGlobals,
                                hfreshLeft, hfreshRight, updateCrepLocal,
                                restoreCrepResult] at hcrep
                              have hrestore :
                                  restoreCrepLocal
                                      (restoreCrepLocal
                                        (updateCrepLocal
                                          (updateCrepLocal state.locals
                                            (context.maxVar + 1) left)
                                          (context.maxVar + 2) right)
                                        (context.maxVar + 2) none)
                                      (context.maxVar + 1) none = state.locals := by
                                funext current
                                by_cases hcurrentRight : current = context.maxVar + 2
                                · subst current
                                  simp [restoreCrepLocal, hfreshRight]
                                · by_cases hcurrentLeft : current = context.maxVar + 1 <;>
                                    simp [restoreCrepLocal, updateCrepLocal,
                                      hcurrentRight, hcurrentLeft, hfreshLeft]
                              rw [hrestore] at hcrep
                              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                hsourceValue, panValuePayloadWithinLimit] at hsource
                              have hsourceEq := hsource.2
                              have hcrepEq := hcrep
                              cases hsourceEq
                              cases hcrepEq
                              have hstate : panValueCrepRaisedStateRel structs context
                                  sourceGlobals sourceMemory
                                  { state with
                                      globals :=
                                        updateMemory
                                          (updateMemory state.globals 0 left)
                                          (0 + bytesInWord) right } 0 := by
                                refine ⟨hrel.1,
                                  panValueCrepLocalsRel_empty structs context state.locals,
                                  ?_⟩
                                intro address _
                                exact congrFun hrel.2.2 address
                              exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_three_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (first second third : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none ∧
      state.locals (context.maxVar + 3) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception
        (.rStruct [.word first, .word second, .word third]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception
        (.rStruct [.const first, .const second, .const third])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const first, .const second, .const third]) =
            some (.rStruct [.word first, .word second, .word third]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context
              (.rStruct [.const first, .const second, .const third]) =
            ([.const first, .const second, .const third],
              .comb [.one, .one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word first, .word second, .word third]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const first, .const second, .const third] =
              some [first, second, third] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const first : CrepExp α), .const second, .const third].length =
            Shape.shapeSize (.comb [.one, .one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 3 1,
          ∀ expression ∈
            ([.const first, .const second, .const third] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 3 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1
            (And.intro (hfresh context state).2.1 (hfresh context state).2.2)
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 3 1 =
          [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception
            (.rStruct [.const first, .const second, .const third])) =
          .seq
            (nestedDecs
              [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3]
              [.const first, .const second, .const third]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2),
                    .var (context.maxVar + 3)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState] at hcrep
                          | succ targetFuel =>
                              cases targetFuel with
                              | zero =>
                                  rw [hcompileProg] at hcrep
                                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                                    evalCrepFullProgState, evalCrepFullExpState,
                                    updateCrepLocal, restoreCrepResult] at hcrep
                              | succ targetFuel =>
                                  cases targetFuel with
                                  | zero =>
                                      rw [hcompileProg] at hcrep
                                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                                        evalCrepFullProgState, evalCrepFullExpState,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                  | succ targetFuel =>
                                      rw [hcompileProg] at hcrep
                                      have hfreshFirst :
                                          state.locals (context.maxVar + 1) = none := by
                                        exact (hfresh context state).1
                                      have hfreshSecond :
                                          state.locals (context.maxVar + 2) = none := by
                                        exact (hfresh context state).2.1
                                      have hfreshThird :
                                          state.locals (context.maxVar + 3) = none := by
                                        exact (hfresh context state).2.2
                                      simp [evalCrepFullProgState,
                                        evalCrepFullExpState, nestedDecs,
                                        crepNestedSeq, storeGlobals,
                                        hfreshFirst, hfreshSecond, hfreshThird,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                      have hrestore :
                                          restoreCrepLocal
                                              (restoreCrepLocal
                                                (restoreCrepLocal
                                                  (updateCrepLocal
                                                    (updateCrepLocal
                                                      (updateCrepLocal state.locals
                                                        (context.maxVar + 1) first)
                                                      (context.maxVar + 2) second)
                                                    (context.maxVar + 3) third)
                                                  (context.maxVar + 3) none)
                                                (context.maxVar + 2) none)
                                              (context.maxVar + 1) none =
                                            state.locals := by
                                        funext current
                                        by_cases hcurrentThird :
                                            current = context.maxVar + 3
                                        · subst current
                                          simp [restoreCrepLocal, hfreshThird]
                                        · by_cases hcurrentSecond :
                                            current = context.maxVar + 2
                                          · subst current
                                            simp [restoreCrepLocal, hfreshSecond]
                                          · by_cases hcurrentFirst :
                                              current = context.maxVar + 1 <;>
                                              simp [restoreCrepLocal,
                                                updateCrepLocal, hcurrentThird,
                                                hcurrentSecond, hcurrentFirst,
                                                hfreshFirst]
                                      rw [hrestore] at hcrep
                                      simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hsourceValue, panValuePayloadWithinLimit] at hsource
                                      have hsourceEq := hsource.2
                                      have hcrepEq := hcrep
                                      cases hsourceEq
                                      cases hcrepEq
                                      have hstate :
                                          panValueCrepRaisedStateRel structs context
                                            sourceGlobals sourceMemory
                                            { state with
                                                globals :=
                                                  updateMemory
                                                    (updateMemory
                                                      (updateMemory state.globals 0 first)
                                                      (0 + bytesInWord) second)
                                                    ((0 + bytesInWord) + bytesInWord)
                                                      third } 0 := by
                                        refine ⟨hrel.1,
                                          panValueCrepLocalsRel_empty structs context
                                            state.locals, ?_⟩
                                        intro address _
                                        exact congrFun hrel.2.2 address
                                      exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_four_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (first second third fourth : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none ∧
      state.locals (context.maxVar + 3) = none ∧
      state.locals (context.maxVar + 4) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception
        (.rStruct [.word first, .word second, .word third, .word fourth])
        exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception
        (.rStruct [.const first, .const second, .const third, .const fourth])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const first, .const second, .const third, .const fourth]) =
            some (.rStruct [.word first, .word second, .word third, .word fourth]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context
              (.rStruct [.const first, .const second, .const third, .const fourth]) =
            ([.const first, .const second, .const third, .const fourth],
              .comb [.one, .one, .one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word first, .word second, .word third, .word fourth]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const first, .const second, .const third, .const fourth] =
              some [first, second, third, fourth] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const first : CrepExp α), .const second, .const third,
            .const fourth].length =
            Shape.shapeSize (.comb [.one, .one, .one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 4 1,
          ∀ expression ∈
            ([.const first, .const second, .const third, .const fourth] :
              List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 4 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1
            (And.intro (hfresh context state).2.1
              (And.intro (hfresh context state).2.2.1 (hfresh context state).2.2.2))
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 4 1 =
          [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3,
            context.maxVar + 4] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception
            (.rStruct [.const first, .const second, .const third, .const fourth])) =
          .seq
            (nestedDecs
              [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3,
                context.maxVar + 4]
              [.const first, .const second, .const third, .const fourth]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2),
                    .var (context.maxVar + 3), .var (context.maxVar + 4)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState] at hcrep
                          | succ targetFuel =>
                              cases targetFuel with
                              | zero =>
                                  rw [hcompileProg] at hcrep
                                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                                    evalCrepFullProgState] at hcrep
                              | succ targetFuel =>
                                  cases targetFuel with
                                  | zero =>
                                      rw [hcompileProg] at hcrep
                                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                                        evalCrepFullProgState, evalCrepFullExpState,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                  | succ targetFuel =>
                                      cases targetFuel with
                                      | zero =>
                                          rw [hcompileProg] at hcrep
                                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                                            evalCrepFullProgState, evalCrepFullExpState,
                                            updateCrepLocal, restoreCrepResult] at hcrep
                                      | succ targetFuel =>
                                          cases targetFuel with
                                          | zero =>
                                              rw [hcompileProg] at hcrep
                                              simp [nestedDecs, crepNestedSeq,
                                                storeGlobals, evalCrepFullProgState,
                                                evalCrepFullExpState,
                                                updateCrepLocal, restoreCrepResult] at hcrep
                                          | succ targetFuel =>
                                              rw [hcompileProg] at hcrep
                                              have hfreshFirst :
                                                  state.locals (context.maxVar + 1) = none := by
                                                exact (hfresh context state).1
                                              have hfreshSecond :
                                                  state.locals (context.maxVar + 2) = none := by
                                                exact (hfresh context state).2.1
                                              have hfreshThird :
                                                  state.locals (context.maxVar + 3) = none := by
                                                exact (hfresh context state).2.2.1
                                              have hfreshFourth :
                                                  state.locals (context.maxVar + 4) = none := by
                                                exact (hfresh context state).2.2.2
                                              simp [evalCrepFullProgState,
                                                evalCrepFullExpState, nestedDecs,
                                                crepNestedSeq, storeGlobals,
                                                hfreshFirst, hfreshSecond, hfreshThird,
                                                hfreshFourth, updateCrepLocal,
                                                restoreCrepResult] at hcrep
                                              have hrestore :
                                                  restoreCrepLocal
                                                      (restoreCrepLocal
                                                        (restoreCrepLocal
                                                          (restoreCrepLocal
                                                            (updateCrepLocal
                                                              (updateCrepLocal
                                                                (updateCrepLocal
                                                                  (updateCrepLocal state.locals
                                                                    (context.maxVar + 1) first)
                                                                  (context.maxVar + 2) second)
                                                                (context.maxVar + 3) third)
                                                              (context.maxVar + 4) fourth)
                                                            (context.maxVar + 4) none)
                                                          (context.maxVar + 3) none)
                                                        (context.maxVar + 2) none)
                                                      (context.maxVar + 1) none =
                                                    state.locals := by
                                                funext current
                                                by_cases hcurrentFourth :
                                                    current = context.maxVar + 4
                                                · subst current
                                                  simp [restoreCrepLocal, hfreshFourth]
                                                · by_cases hcurrentThird :
                                                    current = context.maxVar + 3
                                                  · subst current
                                                    simp [restoreCrepLocal, hfreshThird]
                                                  · by_cases hcurrentSecond :
                                                      current = context.maxVar + 2
                                                    · subst current
                                                      simp [restoreCrepLocal, hfreshSecond]
                                                    · by_cases hcurrentFirst :
                                                        current = context.maxVar + 1 <;>
                                                        simp [restoreCrepLocal,
                                                          updateCrepLocal,
                                                          hcurrentFourth,
                                                          hcurrentThird,
                                                          hcurrentSecond,
                                                          hcurrentFirst,
                                                          hfreshFirst]
                                              rw [hrestore] at hcrep
                                              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                                hsourceValue, panValuePayloadWithinLimit] at hsource
                                              have hsourceEq := hsource.2
                                              have hcrepEq := hcrep
                                              cases hsourceEq
                                              cases hcrepEq
                                              have hstate :
                                                  panValueCrepRaisedStateRel structs context
                                                    sourceGlobals sourceMemory
                                                    { state with
                                                        globals :=
                                                          updateMemory
                                                            (updateMemory
                                                              (updateMemory
                                                                (updateMemory state.globals 0 first)
                                                                (0 + bytesInWord) second)
                                                              ((0 + bytesInWord) + bytesInWord)
                                                                third)
                                                            (((0 + bytesInWord) + bytesInWord) +
                                                              bytesInWord) fourth } 0 := by
                                                refine ⟨hrel.1,
                                                  panValueCrepLocalsRel_empty structs context
                                                    state.locals, ?_⟩
                                                intro address _
                                                exact congrFun hrel.2.2 address
                                              exact ⟨0, hstate, hexception'⟩

end Flapjack
