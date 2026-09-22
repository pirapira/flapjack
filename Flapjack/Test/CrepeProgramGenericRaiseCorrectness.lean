import Flapjack.CrepeProgramGenericRaiseCorrectness
import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.PanCrepSemanticAgreement
import Flapjack.PanStructs

/-! Concrete non-word/non-two-word evidence for the generic structured Raise
    evaluator theorem.  The source payload has three words, so this cannot be
    discharged by either of the specialized one- or two-word Raise lemmas. -/

namespace Flapjack.Test.CrepeProgramGenericRaiseCorrectness

open Flapjack

def context : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 8 }

def state : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

def sourceValue : PanValue Nat :=
  .rStruct [.word 3, .word 4, .word 5]

def sourceExpression : Exp Nat :=
  .rStruct [.const 3, .const 4, .const 5]

def pcGlobalsLookup (_state : CrepState Nat) (value : PanValue Nat) :
    Option (List Nat) :=
  some (panValueFlatWords value)

#check @Flapjack.panValuePcClockedRaisedResultRel_of_hraise_data

example
    {σ : Type} (panHooks : PanSemanticsHooks Nat σ)
    (crepHooks : CrepSemanticsHooks Nat)
    (hcorrect : PanValuePcCompileCorrectWithContextCode
      (fun _ _ _ => none) (fun _ _ _ => none)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ => some 9) pcGlobalsLookup (.raise "E" sourceExpression))
    (evidence : PanValuePcSemanticClockEvidence [] context
      (.raise "E" sourceExpression) 1
      (fun _ _ _ => none) (fun _ _ _ => none)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ code => code = 9) (fun _ => some 9) pcGlobalsLookup
      panHooks crepHooks)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceOutcome : PanSemanticOutcome) (targetOutcome : CrepSemanticOutcome)
    (hsourceOutcome : panResultOutcome panHooks
      (some (evidence.outcome, evidence.returnedClock)) = some sourceOutcome)
    (htargetOutcome : crepResultOutcome
      (crepControlResultToSemantic (some evidence.result)) = some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  exact PanValuePcSemanticClockEvidence.semanticOutcomeRel_withContextCode
    hcorrect 1 evidence hffiOutcome sourceOutcome targetOutcome
    hsourceOutcome htargetOutcome

example
    (hevidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (state : CrepState Nat)
      (baseAddress topAddress bytesInWord : Nat) (sourceValue : PanValue Nat),
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord sourceExpression = some sourceValue →
      ∃ (compiled : List (CrepExp Nat)) (shape : Shape) (values : List Nat),
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context sourceExpression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state baseAddress topAddress compiled =
          some values ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none))
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceValue : PanValue Nat) (exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" sourceValue exceptionCode) :
    PanValueCrepProgramStateCorrect (.raise "E" sourceExpression) := by
  exact panValueCrepProgramStateCorrect_raise_of_compiled_evidence
    "E" sourceExpression hevidence hlookupException hexception

theorem three_word_raise_state_relation :
    ∃ exceptionCode,
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" sourceExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" sourceValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 8 state
        (compileProg context (.raise "E" sourceExpression)) =
        some (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5] } exceptionCode) := by
  let exceptionCode : Nat := 9
  have h := compile_full_pan_value_raise_state_relation_of_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := exceptionCode)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = exceptionCode)
    (hlookup := by simp [context, lookupInfo, exceptionCode])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by
      simp [context, freshNames])
    (hfresh := by
      simp [context, state, freshNames])
    (hexception := by simp [exceptionCode])
  refine ⟨exceptionCode, ?_, ?_⟩
  · simpa [exceptionCode, sourceExpression, sourceValue] using h.1
  · simpa [exceptionCode, sourceExpression, sourceValue, context, freshNames,
      List.range, List.range.loop, Nat.add_assoc] using h.2.1

theorem three_word_raise_pc_hraise :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] } 9 ∧
      lookupInfo "E" context.exceptions = some 9 := by
  have h := panValuePcRaisedGenericHraise_of_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hlookupPayload := by
      intro _
      rfl)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
  simpa [sourceValue, context, pcGlobalsLookup, panValueFlatWords,
    updateMemoryListAt, List.range, List.range.loop, Nat.add_assoc] using h

theorem three_word_raise_pc_result_rel_of_generic_evidence :
    panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9) := by
  have h := panValuePcResultRel_of_raised_generic_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hlookupPayload := by
      intro _
      rfl)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
  simpa [sourceValue, context, pcGlobalsLookup, panValueFlatWords,
    updateMemoryListAt, List.range, List.range.loop, Nat.add_assoc] using h

theorem three_word_raise_generic_semantic_global_lift :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" sourceExpression) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" sourceValue) ∧
    evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0
        (3 + (freshNames context 3 1).length + 2) state
        (compileProg context (.raise "E" sourceExpression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5] } 9) ∧
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5] } 9) := by
  apply panValuePcRaisedGenericSemanticLift_flat_globals_with_context_code
    (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by rfl)
    (hdistinct := by decide)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])


theorem three_word_raise_pc_hraise_global_spill :
    (panValuePcRaisedHraiseData
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcThreeWordGlobalsLookup 8) [] context
        (fun _ _ code => code = 9)
        (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9) ∧
      lookupInfo "E" context.exceptions = some 9 := by
  have h := panValuePcRaisedThreeWordHraise_of_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (first := 3) (second := 4) (third := 5)
    (expression := sourceExpression)
    (compiledFirst := .const 3) (compiledSecond := .const 4)
    (compiledThird := .const 5)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct01 := by decide)
    (hdistinct02 := by decide)
    (hdistinct12 := by decide)
  simpa [sourceValue, context, updateMemoryListAt, List.range,
    List.range.loop, Nat.add_assoc] using h

theorem three_word_raise_pc_semantic_lift :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        (.raise "E" sourceExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" sourceValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 8 state
        (compileProg context (.raise "E" sourceExpression)) =
        some (.raised
          { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
          9) ∧
      panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcThreeWordGlobalsLookup 8)
        (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
          "E" sourceValue)
        (.raised
          { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
          9) := by
  have h := panValuePcRaisedThreeWordSemanticLift
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => some (.word 7)) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (first := 3) (second := 4) (third := 5)
    (expression := sourceExpression)
    (compiledFirst := .const 3) (compiledSecond := .const 4)
    (compiledThird := .const 5)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, ?_, rfl⟩
      intro name value shape slots _ hlookup
      simp [context, lookupInfo] at hlookup)
    (hsource := by
      simp [sourceExpression, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct01 := by decide)
    (hdistinct02 := by decide)
    (hdistinct12 := by decide)
  rcases h with ⟨hsourceEval, htargetEval, hcontext⟩
  refine ⟨hsourceEval, htargetEval, ?_⟩
  simpa [panValuePcResultRel, panValuePcResultRelWithContextCode] using
    (show panValueCrepStateRel [] context
        (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] } ∧
      panValuePcExceptionResultRelWithContextCode [] context (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcThreeWordGlobalsLookup 8) (fun _ => none) (fun _ => none)
        "E" sourceValue
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9 from
      ⟨hcontext.1, hcontext.2⟩)

theorem three_word_raise_pc_hraise_flat_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  have h := panValuePcRaisedGenericHraise_of_flat_globals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hvalues := by
      simp [sourceValue, panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by
      decide)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
  simpa [sourceValue, context, updateMemoryListAt, List.range,
    List.range.loop, Nat.add_assoc] using h

theorem three_word_raise_pc_hraise_retargeted_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := sourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state sourceValue (by decide)
    simpa [pcGlobalsLookup, sourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
  · exact three_word_raise_pc_hraise_flat_globals

theorem three_word_raise_pc_result_rel_flat_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := crepPcFlatGlobalsLookup 8)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := sourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] })
    (targetException := 9)
  exact three_word_raise_pc_hraise_flat_globals

theorem three_word_raise_pc_hraise_retargeted_generic :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  apply panValuePcRaisedGenericHraise_of_evidence_retarget_globals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by
      simp [sourceValue, panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
    (hlookupGlobals := by
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) context.bytesInWord state sourceValue (by decide)
      simpa [context, pcGlobalsLookup, sourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)

theorem three_word_raise_pc_result_rel_retargeted_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9) := by
  have hraiseData :
      panValuePcRaisedHraiseData
        (fun exception => if exception = "E" then some 9 else none)
        pcGlobalsLookup [] context
        (fun _ _ code => code = 9)
        (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9 := by
    apply panValuePcRaisedGenericHraise_of_evidence_retarget_globals
      (context := context) (structs := [])
      (sourceFunctions := []) (functions := [])
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (state := state)
      (primitive := fun _ _ => none)
      (sourceHandler := fun _ _ _ _ _ _ => none)
      (crepPrimitive := fun _ _ => none)
      (ffi := fun _ _ _ _ _ _ => none)
      (sharedMem := fun _ _ _ _ => none)
      (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
      (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
      (expression := sourceExpression) (sourceValue := sourceValue)
      (compiled := [.const 3, .const 4, .const 5])
      (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
      (exceptionRel := fun _ _ code => code = 9)
      (resultExceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (globalsLookup := pcGlobalsLookup)
      (hlookup := by simp [context, lookupInfo])
      (hrel := by
        refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
      (hsource := by
        simp [sourceExpression, sourceValue, evalPanValueExp,
          evalPanValueExp.evalPanValueExps])
      (hvalid := by
        simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
      (hcompile := by
        simp [context, sourceExpression, compileExp,
          compileExp.compileExpList])
      (hlength := by simp [Shape.shapeSize])
      (hcompiled := by
        simp [state, evalCrepFullExpsState, evalCrepFullExpState])
      (hnot := by simp [context, freshNames])
      (hfresh := by simp [context, state, freshNames])
      (hexception := by simp)
      (hcode := by simp)
      (hflat := by
        simp [sourceValue, panValueFlatWords, panValueFlatWordsFuel,
          panValueFlatValueFuel,
          panValueFlatWordsFuel.panValueFlatWordsListFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel])
      (hdistinct := by decide)
      (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
      (hlookupGlobals := by
        have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
          (α := Nat) context.bytesInWord state sourceValue (by decide)
        simpa [context, pcGlobalsLookup, sourceValue, panValueFlatWords,
          panValueFlatWordsFuel, panValueFlatValueFuel,
          panValueFlatWordsFuel.panValueFlatWordsListFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)
  exact panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := sourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] })
    (targetException := 9) hraiseData

theorem three_word_raise_pc_context_code_retargeted_generic :
    panValuePcExceptionResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  apply panValuePcExceptionResultRelWithContextCode_of_raised_generic_evidence
    (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := sourceExpression) (sourceValue := sourceValue)
    (compiled := [.const 3, .const 4, .const 5])
    (shape := .comb [.one, .one, .one]) (values := [3, 4, 5])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [sourceExpression, sourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [sourceValue, panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, sourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by
      simp [sourceValue, panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide)
    (hsize := by simp [sourceValue, panValueShape, Shape.shapeSize])
    (hlookupGlobals := by
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) context.bytesInWord state sourceValue (by decide)
      simpa [context, pcGlobalsLookup, sourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)

def fourWordSourceValue : PanValue Nat :=
  .rStruct [.word 3, .word 4, .word 5, .word 6]

def fourWordSourceExpression : Exp Nat :=
  .rStruct [.const 3, .const 4, .const 5, .const 6]

theorem named_struct_raise_compile_fallback :
    compileExp context (.nStruct "S" [("field", .const 3)]) =
      ([.const 0], .one) := by
  simp [compileExp]

def namedStructPassContext : StructPassContext :=
  { structs := [("S", { fields := [("field", .one)], size := 1 })]
    locals := [], globals := [] }

def namedStructPostPassExpression : Exp Nat :=
  structCompileExp namedStructPassContext
    (.nStruct "S" [("field", .const 3)])

def namedStructPostPassValue : PanValue Nat :=
  .rStruct [.word 3]

def namedStructSourceValue : PanValue Nat :=
  .nStruct "S" [("field", .word 3)]

theorem named_struct_source_pass_one_word_expression (value : Nat) :
    structCompileExp namedStructPassContext
        (.nStruct "S" [("field", .const value)]) =
      .rStruct [.const value] := by
  simp [namedStructPassContext, structCompileExp,
    structCompileExp.structCompileFields, structSelectFields, lookupInfo]

theorem named_struct_source_pass_one_word_flat_words (value : Nat) :
    panValueFlatWords (.nStruct "S" [("field", .word value)]) =
      panValueFlatWords (.rStruct [.word value]) := by
  have hn := panValueFlatWords_nStruct_word_fields "S" [("field", value)]
  have hr := panValueFlatWords_rStruct_word_list [value]
  simpa using hn.trans hr.symm

theorem named_struct_flat_words_word_fields
    (values : List (FieldName × Nat)) :
    panValueFlatWords
        (.nStruct "S"
          (values.map (fun (field, value) => (field, .word value)))) =
      values.map Prod.snd := by
  exact panValueFlatWords_nStruct_word_fields "S" values

theorem named_struct_source_eval_via_generic_evidence (value : Nat) :
    evalPanValueExp namedStructPassContext.structs
        (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (.nStruct "S" [("field", .const value)]) =
        some (.nStruct "S" [("field", .word value)]) := by
  apply evalPanValueExp_nStruct_of_fields_evidence
    (info := { fields := [("field", .one)], size := 1 })
  · simp [namedStructPassContext, lookupInfo]
  · simp [evalPanValueExp.evalPanValueFields, evalPanValueExp]
  · simp [namedStructPassContext, panValueFieldsHaveShapes, panValueShape,
      panShapeMatches]

theorem named_struct_source_pass_one_word_eval (value : Nat) :
    evalPanValueExp namedStructPassContext.structs
        (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (.nStruct "S" [("field", .const value)]) =
        some (.nStruct "S" [("field", .word value)]) ∧
    evalPanValueExp [] (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (structCompileExp namedStructPassContext
          (.nStruct "S" [("field", .const value)])) =
        some (.rStruct [.word value]) := by
  refine ⟨named_struct_source_eval_via_generic_evidence value, ?_⟩
  simp [namedStructPassContext, structCompileExp,
    structCompileExp.structCompileFields, structSelectFields, lookupInfo,
    evalPanValueExp, evalPanValueExp.evalPanValueExps]

theorem named_struct_source_pass_full_raise_state_relation :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" namedStructPostPassExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" namedStructPostPassValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 4 state
        (compileProg context (.raise "E" namedStructPostPassExpression)) =
        some (.raised
          { state with globals := updateMemoryListAt state.globals 0 8 [3] }
          9) := by
  have h := compile_full_pan_value_raise_state_relation_of_struct_pass_evidence
    (α := Nat) (context := context)
    (sourceStructs := namedStructPassContext.structs) (postStructs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (name := "S") (fields := [("field", .const 3)])
    (values := [("field", .word 3)])
    (info := { fields := [("field", .one)], size := 1 })
    (postExpression := namedStructPostPassExpression)
    (postValue := namedStructPostPassValue)
    (compiled := [.const 3]) (shape := .comb [.one]) (flatValues := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (hlookupException := by simp [context, lookupInfo])
    (hlookupStruct := by simp [namedStructPassContext, lookupInfo])
    (hfields := by
      simp [evalPanValueExp.evalPanValueFields, evalPanValueExp])
    (hshape := by
      simp [namedStructPassContext, panValueFieldsHaveShapes, panValueShape,
        panShapeMatches])
    (hpass := by
      intro namedValue hnamed
      have hsource := named_struct_source_eval_via_generic_evidence 3
      have hvalue : namedValue = namedStructSourceValue :=
        Option.some.inj (hnamed.symm.trans hsource)
      subst namedValue
      exact (named_struct_source_pass_one_word_eval 3).2)
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hvalid := by
      simp [namedStructPostPassValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp only [namedStructPostPassExpression]
      rw [named_struct_source_pass_one_word_expression 3]
      simp [context, compileExp, compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hflat := by
      simp [namedStructPostPassValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
  refine ⟨?_, ?_⟩
  · simpa [namedStructPostPassExpression, namedStructPostPassValue,
      namedStructPassContext, structCompileExp,
      structCompileExp.structCompileFields, structSelectFields, lookupInfo,
      compileExp, compileExp.compileExpList] using h.1
  · simpa [context, namedStructPostPassExpression, namedStructPostPassValue,
      namedStructPassContext, structCompileExp,
      structCompileExp.structCompileFields, structSelectFields, lookupInfo,
      compileExp, compileExp.compileExpList, freshNames, List.range,
      List.range.loop, Nat.add_assoc] using h.2.1

theorem named_struct_source_pass_generic_hraise_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      namedStructPostPassValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] } 9 ∧
    lookupInfo "E" context.exceptions = some 9 := by
  apply panValuePcRaisedGenericHraise_of_struct_pass_evidence
    (α := Nat) (context := context)
    (sourceStructs := namedStructPassContext.structs) (postStructs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (name := "S") (fields := [("field", .const 3)])
    (values := [("field", .word 3)])
    (info := { fields := [("field", .one)], size := 1 })
    (postExpression := namedStructPostPassExpression)
    (postValue := namedStructPostPassValue)
    (compiled := [.const 3]) (shape := .comb [.one]) (flatValues := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookupException := by simp [context, lookupInfo])
    (hlookupStruct := by simp [namedStructPassContext, lookupInfo])
    (hfields := by
      simp [evalPanValueExp.evalPanValueFields, evalPanValueExp])
    (hshape := by
      simp [namedStructPassContext, panValueFieldsHaveShapes, panValueShape,
        panShapeMatches])
    (hpass := by
      intro namedValue hnamed
      have hsource := named_struct_source_eval_via_generic_evidence 3
      have hvalue : namedValue = namedStructSourceValue :=
        Option.some.inj (hnamed.symm.trans hsource)
      subst namedValue
      exact (named_struct_source_pass_one_word_eval 3).2)
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hvalid := by
      simp [namedStructPostPassValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp only [namedStructPostPassExpression]
      rw [named_struct_source_pass_one_word_expression 3]
      simp [context, compileExp, compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hflat := by
      simp [namedStructPostPassValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hlookupPayload := by
      intro _
      rfl)
    (hsize := by
      simp [namedStructPostPassValue, panValueShape, Shape.shapeSize])

/-! The stateful constructor also handles a record whose fields are nested
    scalar expressions rather than constants.  The source evaluator is kept
    as an explicit oracle regression so this test exercises both the
    field-list inversion and the scalar compiler relation. -/
def scalarSourceWordFields : List (SourceWordExp Nat) :=
  [ .op .add (.const 3) (.const 4),
    .mul (.op .add (.const 1) (.const 2)) (.const 5) ]

def scalarSourceWordRaise : Prog Nat :=
  .raise "E" (.rStruct (scalarSourceWordFields.map SourceWordExp.toExp))

theorem scalar_source_word_fields_oracle :
    evalPanValueExp [] (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (scalarSourceWordFields.map SourceWordExp.toExp
          |> fun fields => .rStruct fields) =
      some (.rStruct [.word 7, .word 15]) := by
  simp [scalarSourceWordFields, SourceWordExp.toExp, evalPanValueExp,
    evalPanValueExp.evalPanValueExps, evalPanBinOp]

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hbounded : ∀ (context : CompileContext Nat) (name : VarName)
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      ∀ slot ∈ slots, slot ≤ context.maxVar)
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat)
      (name : Nat), name ∈ freshNames context scalarSourceWordFields.length 1 →
      state.locals name = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (exceptionCode : Nat) (values : List Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" (.rStruct (values.map PanValue.word)) exceptionCode) :
    PanValueCrepProgramStateCorrect scalarSourceWordRaise := by
  exact panValueCrepProgramStateCorrect_raise_source_word_record
    "E" scalarSourceWordFields hbytesInWord hlookup hbounded
    hlookupException hfresh hexception

theorem named_struct_source_pass_compile_raise (value : Nat) :
    compileProg context
        (.raise "E"
          (structCompileExp namedStructPassContext
            (.nStruct "S" [("field", .const value)]))) =
      .seq
        (nestedDecs [context.maxVar + 1] [.const value]
          (crepNestedSeq
            (storeGlobals 0 context.bytesInWord
              [.var (context.maxVar + 1)])))
        (.raise 9) := by
  simp [context, namedStructPassContext, structCompileExp,
    structCompileExp.structCompileFields, structSelectFields, lookupInfo,
    compileProg, compileExp, compileExp.compileExpList, freshNames,
    List.range, List.range.loop, nestedDecs, crepNestedSeq, storeGlobals,
    Shape.shapeSize]

theorem named_struct_source_pass_raise_pc_relation (value : Nat) :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E"
          (structCompileExp namedStructPassContext
            (.nStruct "S" [("field", .const value)]))) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" (.rStruct [.word value])) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 4 state
        (compileProg context
          (.raise "E"
            (structCompileExp namedStructPassContext
              (.nStruct "S" [("field", .const value)])))) =
        some (.raised
          { state with globals := updateMemoryListAt state.globals 0 8 [value] }
          9) ∧
      panValuePcResultRel [] context (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        pcGlobalsLookup
        (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
          (.rStruct [.word value]))
        (.raised
          { state with globals := updateMemoryListAt state.globals 0 8 [value] }
          9) := by
  have hevidence := compile_full_pan_value_raise_state_relation_of_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := structCompileExp namedStructPassContext
      (.nStruct "S" [("field", .const value)]))
    (sourceValue := .rStruct [.word value])
    (compiled := [.const value]) (shape := .comb [.one]) (values := [value])
    (exceptionRel := fun _ _ code => code = 9)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      apply evalPanValueExp_structPass_of_named_fields_evidence
        (sourceStructs := namedStructPassContext.structs) (postStructs := [])
        (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
        (sourceMemory := fun _ => none)
        (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
        (name := "S")
        (fields := [("field", .const value)])
        (values := [("field", .word value)])
        (info := { fields := [("field", .one)], size := 1 })
        (postExpression := structCompileExp namedStructPassContext
          (.nStruct "S" [("field", .const value)]))
        (postValue := .rStruct [.word value])
      · simp [namedStructPassContext, lookupInfo]
      · simp [evalPanValueExp.evalPanValueFields, evalPanValueExp]
      · simp [namedStructPassContext, panValueFieldsHaveShapes, panValueShape,
          panShapeMatches]
      · intro namedValue _
        simp [namedStructPassContext, structCompileExp,
          structCompileExp.structCompileFields, structSelectFields, lookupInfo,
          evalPanValueExp, evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, namedStructPassContext, structCompileExp,
        structCompileExp.structCompileFields, structSelectFields, lookupInfo,
        compileExp, compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
  refine ⟨?_, ?_, ?_⟩
  · simpa [namedStructPassContext] using hevidence.1
  · simpa [context, freshNames, List.range, List.range.loop, Nat.add_assoc]
      using hevidence.2.1
  · apply panValuePcResultRel_of_raised_hraise_data
      (structs := []) (context := context)
      (exceptionRel := fun _ _ code => code = 9)
      (exceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (globalsLookup := pcGlobalsLookup)
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (sourceException := "E")
      (sourceValue := .rStruct [.word value])
      (targetState :=
        { state with globals := updateMemoryListAt state.globals 0 8 [value] })
      (targetException := 9)
    apply panValuePcRaisedHraiseData_retarget_globals_lookup
      (bytesInWord := 8) (structs := []) (context := context)
      (exceptionRel := fun _ _ code => code = 9)
      (exceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (globalsLookup := pcGlobalsLookup)
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (sourceException := "E")
      (sourceValue := .rStruct [.word value])
      (targetState :=
        { state with globals := updateMemoryListAt state.globals 0 8 [value] })
      (targetException := 9)
    · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) 8 state (.rStruct [.word value]) (by
          simp [storeAddresses, panValueFlatWords, panValueFlatWordsFuel,
            panValueFlatValueFuel,
            panValueFlatWordsFuel.panValueFlatWordsListFuel,
            panValueFlatValueFuel.panValueFlatValueListFuel])
      simpa [pcGlobalsLookup, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
    · exact panValuePcRaisedHraiseData_of_flat_spill_state
        (structs := []) (context := context)
        (exceptionRel := fun _ _ code => code = 9)
        (exceptionCode := fun exception =>
          if exception = "E" then some 9 else none)
        (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
        (sourceMemory := fun _ => none) (sourceException := "E")
        (values := [value]) (state := state) (bytesInWord := 8)
        (targetException := 9) (sourceValue := .rStruct [.word value])
        (hrel := by
          refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩)
        (hexception := by simp)
        (hcode := by simp)
        (hflat := by rfl)
        (hdistinct := by
          simp [storeAddresses])
        (hsize := by simp [panValueShape, Shape.shapeSize])

theorem named_struct_raise_after_struct_pass_hraise_flat_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      namedStructPostPassValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcRaisedGenericHraise_of_evidence_flat_globals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := namedStructPostPassExpression)
    (sourceValue := namedStructPostPassValue)
    (compiled := [.const 3]) (shape := .comb [.one]) (values := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [namedStructPostPassExpression, namedStructPassContext,
        structCompileExp, structCompileExp.structCompileFields,
        structSelectFields, lookupInfo, namedStructPostPassValue,
        evalPanValueExp, evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [namedStructPostPassValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, namedStructPostPassExpression,
        namedStructPassContext, structCompileExp,
        structCompileExp.structCompileFields, structSelectFields,
        lookupInfo, compileExp, compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by rfl)
    (hdistinct := by decide)
    (hsize := by
      simp [namedStructPostPassValue, panValueShape, Shape.shapeSize])

theorem named_struct_word_fields_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      namedStructSourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcRaisedHraiseData_of_named_struct_word_fields
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (name := "S") (fields := [("field", 3)])
    (state := state) (bytesInWord := 8) (targetException := 9)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · decide
  · simp [panValueShape]

theorem named_struct_nested_word_field_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      (.nStruct "Outer" [("inner", .rStruct [.word 3])])
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcRaisedHraiseData_of_named_struct_nested_word_field
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (name := "Outer") (field := "inner") (value := 3)
    (state := state) (bytesInWord := 8) (targetException := 9)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · decide
  · simp [panValueShape]

theorem named_struct_nested_two_word_field_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      (.nStruct "Outer" [("inner", .rStruct [.word 3, .word 4])])
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4] }
      9 := by
  apply panValuePcRaisedHraiseData_of_named_struct_nested_two_word_field
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (name := "Outer") (field := "inner") (left := 3) (right := 4)
    (state := state) (bytesInWord := 8) (targetException := 9)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · decide
  · simp [panValueShape]

theorem named_struct_nested_word_fields_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      (.nStruct "Outer"
        [("left", .rStruct [.word 3]),
          ("right", .rStruct [.word 4])])
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4] }
      9 := by
  apply panValuePcRaisedHraiseData_of_named_struct_nested_word_fields
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (name := "Outer") (leftField := "left") (rightField := "right")
    (left := 3) (right := 4) (state := state) (bytesInWord := 8)
    (targetException := 9)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · decide
  · simp [panValueShape]

theorem named_struct_nested_mixed_fields_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      (.nStruct "Outer"
        [("pair", .rStruct [.word 3, .word 4]),
          ("tail", .rStruct [.word 5])])
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  apply panValuePcRaisedHraiseData_of_named_struct_nested_mixed_fields
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (name := "Outer") (pairField := "pair") (tailField := "tail")
    (first := 3) (second := 4) (third := 5) (state := state)
    (bytesInWord := 8) (targetException := 9)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · decide
  · simp [panValueShape]

theorem generic_flattened_nested_global_bridge :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      (.nStruct "Outer"
        [("pair", .rStruct [.word 3, .word 4]),
          ("tail", .rStruct [.word 5])])
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
  have hgeneric := panValuePcRaisedHraiseData_of_flat_spill_state_auto
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (state := state) (bytesInWord := 8) (targetException := 9)
    (sourceValue :=
      .nStruct "Outer"
        [("pair", .rStruct [.word 3, .word 4]),
          ("tail", .rStruct [.word 5])])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩)
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct := by decide)
    (hsize := by simp [panValueShape])
  simpa [panValueFlatWords, panValueFlatWordsFuel, panValueFlatValueFuel,
    panValueFlatWordsFuel.panValueFlatWordsFieldListFuel,
    panValueFlatWordsFuel.panValueFlatWordsListFuel,
    panValueFlatValueFuel.panValueFlatValueFieldListFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel] using hgeneric

theorem generic_flattened_nested_result_bridge :
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.nStruct "Outer"
          [("pair", .rStruct [.word 3, .word 4]),
            ("tail", .rStruct [.word 5])]))
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
        9) := by
  apply panValuePcResultRelWithContextCode_of_raised_flat_spill_auto
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (state := state) (bytesInWord := 8) (targetException := 9)
    (sourceValue :=
      .nStruct "Outer"
        [("pair", .rStruct [.word 3, .word 4]),
          ("tail", .rStruct [.word 5])])
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩
  · simp
  · simp
  · simp [context, lookupInfo]
  · decide
  · simp [panValueShape]

theorem named_struct_raise_after_struct_pass_result_rel_retargeted_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        namedStructPostPassValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := namedStructPostPassValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := namedStructPostPassValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state namedStructPostPassValue (by decide)
    simpa [pcGlobalsLookup, namedStructPostPassValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
  · exact named_struct_raise_after_struct_pass_hraise_flat_globals

theorem named_struct_raise_after_struct_pass_context_code :
    panValuePcExceptionResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup (fun _ => none) (fun _ => none) "E"
      namedStructPostPassValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := namedStructPostPassValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9) (hraiseEvidence := ?_)
  refine ⟨?_, ?_⟩
  · apply panValuePcRaisedHraiseData_retarget_globals_lookup
      (bytesInWord := 8) (structs := []) (context := context)
      (exceptionRel := fun _ _ code => code = 9)
      (exceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (globalsLookup := pcGlobalsLookup)
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (sourceException := "E")
      (sourceValue := namedStructPostPassValue)
      (targetState :=
        { state with globals := updateMemoryListAt state.globals 0 8 [3] })
      (targetException := 9)
    · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) 8 state namedStructPostPassValue (by decide)
      simpa [pcGlobalsLookup, namedStructPostPassValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
    · exact named_struct_raise_after_struct_pass_hraise_flat_globals
  · simp [context, lookupInfo]

theorem named_struct_raise_pc_result_rel_named_payload_spill :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        namedStructSourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := namedStructSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := namedStructSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state namedStructSourceValue (by decide)
    simpa [pcGlobalsLookup, namedStructSourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsFieldListFuel,
      panValueFlatValueFuel.panValueFlatValueFieldListFuel] using hstored
  · exact panValuePcRaisedHraiseData_of_flat_spill_state
      (structs := []) (context := context)
      (exceptionRel := fun _ _ code => code = 9)
      (exceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (sourceException := "E")
      (values := [3]) (state := state) (bytesInWord := 8)
      (targetException := 9) (sourceValue := namedStructSourceValue)
      (hrel := by
        refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩)
      (hexception := by simp)
      (hcode := by simp)
      (hflat := by rfl)
      (hdistinct := by decide)
      (hsize := by simp [namedStructSourceValue, panValueShape])

theorem four_word_raise_pc_hraise_raw_words :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      fourWordSourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
      9 ∧ lookupInfo "E" context.exceptions = some 9 := by
  apply panValuePcRaisedRawWordListHraise_of_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (values := [3, 4, 5, 6]) (expression := fourWordSourceExpression)
    (compiled := [.const 3, .const 4, .const 5, .const 6])
    (shape := .comb [.one, .one, .one, .one])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [fourWordSourceExpression, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, fourWordSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct := by decide)
    (hsize := by simp [panValueShape, Shape.shapeSize])

theorem four_word_raise_pc_semantic_lift :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        (.raise "E" fourWordSourceExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 10 state
        (compileProg context (.raise "E" fourWordSourceExpression)) =
        some (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) ∧
      panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcFlatGlobalsLookup 8)
        (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue)
        (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) := by
  have h := panValuePcRaisedGenericSemanticLift_flat_globals_with_context_code
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => some (.word 7)) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (sourceValue := fourWordSourceValue)
    (values := [3, 4, 5, 6]) (expression := fourWordSourceExpression)
    (compiled := [.const 3, .const 4, .const 5, .const 6])
    (shape := .comb [.one, .one, .one, .one])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, ?_, rfl⟩
      intro name value shape slots _ hlookup
      simp [context, lookupInfo] at hlookup)
    (hsource := by
      simp [fourWordSourceExpression, fourWordSourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [fourWordSourceValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, fourWordSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by
      simp [fourWordSourceValue, panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide)
    (hsize := by simp [fourWordSourceValue, panValueShape, Shape.shapeSize])
  rcases h with ⟨hsourceEval, htargetEval, hcontext⟩
  simpa [context, fourWordSourceValue, freshNames, List.range, List.range.loop,
    Nat.add_assoc] using ⟨hsourceEval, htargetEval, hcontext⟩

theorem four_word_raise_pc_semantic_lift_retargeted :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        (.raise "E" fourWordSourceExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 10 state
        (compileProg context (.raise "E" fourWordSourceExpression)) =
        some (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) ∧
      panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        pcGlobalsLookup
        (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue)
        (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) := by
  have h := panValuePcRaisedRawWordListSemanticLift_retarget_globals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => some (.word 7)) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (values := [3, 4, 5, 6]) (expression := fourWordSourceExpression)
    (compiled := [.const 3, .const 4, .const 5, .const 6])
    (shape := .comb [.one, .one, .one, .one])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, ?_, rfl⟩
      intro name value shape slots _ hlookup
      simp [context, lookupInfo] at hlookup)
    (hsource := by
      simp [fourWordSourceExpression, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, fourWordSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct := by decide)
    (hsize := by simp [panValueShape, Shape.shapeSize])
    (hlookupGlobals := by
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) context.bytesInWord state fourWordSourceValue (by decide)
      simpa [context, pcGlobalsLookup, fourWordSourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)
  simpa [context, fourWordSourceValue, freshNames, List.range, List.range.loop,
    Nat.add_assoc] using h

theorem four_word_raise_pc_semantic_lift_with_context_code :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        (.raise "E" fourWordSourceExpression) =
        some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue) ∧
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 10 state
        (compileProg context (.raise "E" fourWordSourceExpression)) =
        some (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) ∧
      panValuePcResultRelWithContextCode [] context
        (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
        (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
          "E" fourWordSourceValue)
        (.raised
          { state with globals :=
              updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] } 9) := by
  have h := panValuePcRaisedGenericSemanticLift_retarget_globals_with_context_code
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => some (.word 7)) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (sourceValue := fourWordSourceValue)
    (values := [3, 4, 5, 6]) (expression := fourWordSourceExpression)
    (compiled := [.const 3, .const 4, .const 5, .const 6])
    (shape := .comb [.one, .one, .one, .one])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, ?_, rfl⟩
      intro name value shape slots _ hlookup
      simp [context, lookupInfo] at hlookup)
    (hsource := by
      simp [fourWordSourceExpression, fourWordSourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [fourWordSourceValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, fourWordSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by
      simp [fourWordSourceValue, panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide)
    (hsize := by simp [fourWordSourceValue, panValueShape, Shape.shapeSize])
    (hlookupGlobals := by
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) context.bytesInWord state fourWordSourceValue (by decide)
      simpa [context, pcGlobalsLookup, fourWordSourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)
  simpa [context, fourWordSourceValue, freshNames, List.range, List.range.loop,
    Nat.add_assoc] using h

theorem four_word_raise_pc_context_code_from_evidence :
    panValuePcExceptionResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup (fun _ => none) (fun _ => none) "E"
      fourWordSourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
      9 := by
  apply panValuePcExceptionResultRelWithContextCode_of_raised_raw_word_list_evidence
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (values := [3, 4, 5, 6]) (expression := fourWordSourceExpression)
    (compiled := [.const 3, .const 4, .const 5, .const 6])
    (shape := .comb [.one, .one, .one, .one])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [fourWordSourceExpression, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, fourWordSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hdistinct := by decide)
    (hsize := by simp [panValueShape, Shape.shapeSize])
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state fourWordSourceValue (by decide)
    simpa [context, pcGlobalsLookup, fourWordSourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored

theorem four_word_raise_pc_context_code_from_semantic_lift :
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        "E" fourWordSourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
        9) := by
  apply panValuePcResultRelWithContextCode_of_raised_result_rel
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => some (.word 7)) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := fourWordSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
    (targetException := 9)
  exact ⟨⟨four_word_raise_pc_semantic_lift_retargeted.2.2.1,
      four_word_raise_pc_semantic_lift_retargeted.2.2.2.1⟩, by
    simp [context, lookupInfo]⟩

theorem four_word_raise_pc_hraise_retargeted_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      fourWordSourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
      9 := by
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := fourWordSourceValue)
    (targetState :=
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state fourWordSourceValue (by decide)
    simpa [pcGlobalsLookup, fourWordSourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
  · exact four_word_raise_pc_hraise_raw_words.1

theorem four_word_raise_pc_context_code_retargeted_globals :
    panValuePcExceptionResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup (fun _ => none) (fun _ => none) "E"
      fourWordSourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
      9 := by
  apply panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := fourWordSourceValue)
    (targetState :=
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
    (targetException := 9) (hraiseEvidence := ?_)
  refine ⟨?_, ?_⟩
  · apply panValuePcRaisedHraiseData_retarget_globals_lookup
      (bytesInWord := 8) (structs := []) (context := context)
      (exceptionRel := fun _ _ code => code = 9)
      (exceptionCode := fun exception =>
        if exception = "E" then some 9 else none)
      (globalsLookup := pcGlobalsLookup)
      (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
      (sourceMemory := fun _ => none) (sourceException := "E")
      (sourceValue := fourWordSourceValue)
      (targetState :=
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
      (targetException := 9)
    · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) 8 state fourWordSourceValue (by decide)
      simpa [pcGlobalsLookup, fourWordSourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
    · exact four_word_raise_pc_hraise_raw_words.1
  · simp [context, lookupInfo]

theorem four_word_raise_pc_result_rel_flat_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        fourWordSourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := crepPcFlatGlobalsLookup 8)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := fourWordSourceValue)
    (targetState :=
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
    (targetException := 9)
  exact four_word_raise_pc_hraise_raw_words.1

theorem four_word_raise_pc_result_rel_retargeted_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        fourWordSourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := fourWordSourceValue)
    (targetState :=
      { state with globals :=
          updateMemoryListAt state.globals 0 8 [3, 4, 5, 6] })
    (targetException := 9)
  exact four_word_raise_pc_hraise_retargeted_globals

def nestedSourceValue : PanValue Nat :=
  .rStruct [.rStruct [.word 3]]

def nestedSourceExpression : Exp Nat :=
  .rStruct [.rStruct [.const 3]]

theorem nested_raise_pc_hraise_flat_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      nestedSourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcRaisedGenericHraise_of_evidence_flat_globals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := nestedSourceExpression) (sourceValue := nestedSourceValue)
    (compiled := [.const 3]) (shape := .comb [.comb [.one]]) (values := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [nestedSourceExpression, nestedSourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [nestedSourceValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, nestedSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by
      rfl)
    (hdistinct := by decide)
    (hsize := by simp [nestedSourceValue, panValueShape, Shape.shapeSize])

theorem nested_raise_pc_hraise_retargeted_globals_paired :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      nestedSourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 ∧ lookupInfo "E" context.exceptions = some 9 := by
  apply panValuePcRaisedGenericHraise_of_evidence_retarget_globals_with_source_locals
    (α := Nat) (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := nestedSourceExpression) (sourceValue := nestedSourceValue)
    (compiled := [.const 3]) (shape := .comb [.comb [.one]]) (values := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context _, rfl⟩)
    (hsource := by
      simp [nestedSourceExpression, nestedSourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [nestedSourceValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, nestedSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by rfl)
    (hdistinct := by decide)
    (hsize := by simp [nestedSourceValue, panValueShape, Shape.shapeSize])
    (hlookupGlobals := by
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := Nat) 8 state nestedSourceValue (by decide)
      simpa [context, pcGlobalsLookup, nestedSourceValue, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel] using hstored)

theorem nested_raise_pc_hraise_retargeted_globals :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E"
      nestedSourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3] }
      9 := by
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := nestedSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state nestedSourceValue (by decide)
    simpa [pcGlobalsLookup, nestedSourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
  · exact nested_raise_pc_hraise_flat_globals

theorem nested_flat_globals_lookup_exact :
    crepPcFlatGlobalsLookup 8
        { state with globals := updateMemoryListAt state.globals 0 8 [3] }
        nestedSourceValue =
      pcGlobalsLookup
        { state with globals := updateMemoryListAt state.globals 0 8 [3] }
        nestedSourceValue := by
  have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
    (α := Nat) 8 state nestedSourceValue (by decide)
  simpa [pcGlobalsLookup, nestedSourceValue, panValueFlatWords,
    panValueFlatWordsFuel, panValueFlatValueFuel,
    panValueFlatWordsFuel.panValueFlatWordsListFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel] using hstored

theorem nested_raise_generic_semantic_global_lift :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        0 0 8 3 (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" nestedSourceExpression) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" nestedSourceValue) ∧
    evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0
        (1 + (freshNames context 1 1).length + 2) state
        (compileProg context (.raise "E" nestedSourceExpression)) =
      some (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3] } 9) ∧
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" nestedSourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3] } 9) := by
  apply panValuePcRaisedGenericSemanticLift_flat_globals_with_context_code
    (context := context) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := state)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (exception := "E") (exceptionCode := 9)
    (expression := nestedSourceExpression) (sourceValue := nestedSourceValue)
    (compiled := [.const 3]) (shape := .comb [.comb [.one]]) (values := [3])
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (hlookup := by simp [context, lookupInfo])
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] context state.locals, rfl⟩)
    (hsource := by
      simp [nestedSourceExpression, nestedSourceValue, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [nestedSourceValue, panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
    (hcompile := by
      simp [context, nestedSourceExpression, compileExp,
        compileExp.compileExpList])
    (hlength := by simp [Shape.shapeSize])
    (hcompiled := by
      simp [state, evalCrepFullExpsState, evalCrepFullExpState])
    (hnot := by simp [context, freshNames])
    (hfresh := by simp [context, state, freshNames])
    (hexception := by simp)
    (hcode := by simp)
    (hflat := by rfl)
    (hdistinct := by decide)
    (hsize := by simp [nestedSourceValue, panValueShape, Shape.shapeSize])

theorem three_word_raise_pc_compile_correct_context_code_of_evaluator_evidence
    (sourceFuel targetFuel : Nat)
    (hlookupException : ∀ context : CompileContext Nat,
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat)
      (name : Nat), name ∈ freshNames context 3 1 → state.locals name = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" sourceValue exceptionCode)
    (hevidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState Nat) (expression : Exp Nat)
        (compiled : List (CrepExp Nat)) (shape : Shape),
        targetState =
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                (panValueFlatWords sourceValue)) } ∧
        context.bytesInWord = 8 ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          0 0 8 expression = some sourceValue ∧
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state 0 0 compiled =
          some (panValueFlatWords sourceValue) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        (if sourceException = "E" then some 9 else none) =
          some targetException ∧
        List.Pairwise (fun left right : Nat => left ≠ right)
          (storeAddresses 0 context.bytesInWord
            (panValueFlatWords sourceValue).length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True)
      (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raise "E" sourceExpression) := by
  have hprogram := panValueCrepProgramStateCorrect_raise_word_list_record
    "E" [3, 4, 5] hlookupException hfresh hexception
  have hprogramSafe := panValueCrepProgramStateControlSafe_raise "E"
    sourceExpression
  apply panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_auto_context_code
    (.raise "E" sourceExpression)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) [] []
    (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 0 8 sourceFuel targetFuel
    hprogram hprogramSafe
  · intro targetState sourceValue
    rfl
  · exact hevidence

theorem nested_raise_pc_result_rel_retargeted_globals :
    panValuePcResultRel [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      pcGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        nestedSourceValue)
      (.raised
        { state with globals := updateMemoryListAt state.globals 0 8 [3] }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := nestedSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := context)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := fun exception =>
      if exception = "E" then some 9 else none)
    (globalsLookup := pcGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := nestedSourceValue)
    (targetState :=
      { state with globals := updateMemoryListAt state.globals 0 8 [3] })
    (targetException := 9)
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 state nestedSourceValue (by decide)
    simpa [context, pcGlobalsLookup, nestedSourceValue, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel] using hstored
  · exact nested_raise_pc_hraise_flat_globals

def directClockContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes =>
      match bytes with
      | byte :: _ => byte.toNat
      | [] => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def directClockFfi : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

def directClockHandler : PanValueStatefulFfiHandler Nat Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

theorem three_word_raise_pc_compile_correct_direct_clocked_normal
    (sourceFuel targetFuel : Nat)
    (hlookupException : ∀ context : CompileContext Nat,
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat)
      (name : Nat), name ∈ freshNames context 3 1 → state.locals name = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" sourceValue exceptionCode)
    (hevidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState Nat) (expression : Exp Nat)
        (compiled : List (CrepExp Nat)) (shape : Shape),
        targetState =
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                (panValueFlatWords sourceValue)) } ∧
        context.bytesInWord = 8 ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          0 0 8 expression = some sourceValue ∧
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state 0 0 compiled =
          some (panValueFlatWords sourceValue) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        (if sourceException = "E" then some 9 else none) =
          some targetException ∧
        List.Pairwise (fun left right : Nat => left ≠ right)
          (storeAddresses 0 context.bytesInWord
            (panValueFlatWords sourceValue).length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True)
      (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raise "E" sourceExpression) ∧
    evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 .skip =
      some (.control (.normal (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi), 1) ∧
    panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.normal (fun _ => none) (fun _ => none) (fun _ => none))
      (.normal state) := by
  have hprogram := panValueCrepProgramStateCorrect_raise_word_list_record
    "E" [3, 4, 5] hlookupException hfresh hexception
  have hprogramSafe := panValueCrepProgramStateControlSafe_raise "E"
    sourceExpression
  have hsourceAdapter := fun (context : CompileContext Nat)
      (structs : StructContext) (sourceInput : PanValuePcInput Nat)
      (targetInput : CrepPcInput Nat)
      (sourceExecution : PanValuePcExecution Nat)
      (hstructs : sourceInput.structs = structs)
      (heval : panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel
        context sourceInput (.raise "E" sourceExpression) =
        some sourceExecution) =>
    panValuePcCompactSourceEvaluator_adapter
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel
      (.raise "E" sourceExpression) context structs sourceInput targetInput
      sourceExecution hstructs heval
  have htargetAdapter := fun (context : CompileContext Nat)
      (structs : StructContext) (sourceInput : PanValuePcInput Nat)
      (targetInput : CrepPcInput Nat)
      (targetExecution : CrepPcExecution Nat)
      (hstructs : targetInput.structs = structs)
      (heval : crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel
        context targetInput (compileProg context (.raise "E" sourceExpression)) =
        some targetExecution) =>
    crepPcCompactTargetEvaluator_adapter
      [] (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 targetFuel (.raise "E" sourceExpression) context structs sourceInput
      targetInput targetExecution hstructs heval
  have hclock :
      evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 .skip =
      some (.control (.normal (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi), 1) := by
    simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps]
  have hclockState : panValueCrepStateRel [] context
      (fun _ => none) (fun _ => none) (fun _ => none) state := by
    refine ⟨rfl, ?_, rfl⟩
    exact panValueCrepLocalsRel_empty [] context state.locals
  have hevidenceWithValues :
      ∀ (evidenceContext : CompileContext Nat) (evidenceStructs : StructContext)
        (evidenceExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
        (evidenceLocals evidenceGlobals : VarName → Option (PanValue Nat))
        (evidenceMemory : Nat → Option (PanValue Nat))
        (evidenceException : ExceptionId) (evidenceValue : PanValue Nat)
        (evidenceTargetState : CrepState Nat) (evidenceTargetException : Nat),
        panValueCrepControlRel evidenceStructs evidenceContext
          evidenceExceptionRel
          (.raised evidenceLocals evidenceGlobals evidenceMemory evidenceException
            evidenceValue)
          (.raised evidenceTargetState evidenceTargetException) →
        ∃ (evidenceState : CrepState Nat) (expression : Exp Nat)
          (compiled : List (CrepExp Nat)) (shape : Shape) (values : List Nat),
          evidenceTargetState =
              { evidenceState with globals :=
                  (updateMemoryListAt evidenceState.globals 0
                    evidenceContext.bytesInWord values) } ∧
          evidenceContext.bytesInWord = 8 ∧
          panValueCrepStateRel evidenceStructs evidenceContext evidenceLocals
            evidenceGlobals evidenceMemory evidenceState ∧
          evalPanValueExp evidenceStructs evidenceLocals evidenceGlobals
            evidenceMemory 0 0 8 expression = some evidenceValue ∧
          panValuePayloadWithinLimit evidenceStructs evidenceValue = true ∧
          compileExp evidenceContext expression = (compiled, shape) ∧
          compiled.length = Shape.shapeSize shape ∧
          evalCrepFullExpsState evidenceState 0 0 compiled = some values ∧
          (∀ name ∈ freshNames evidenceContext compiled.length 1,
            ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
          (∀ name ∈ freshNames evidenceContext compiled.length 1,
            evidenceState.locals name = none) ∧
          evidenceExceptionRel evidenceException evidenceValue
            evidenceTargetException ∧
          lookupInfo evidenceException evidenceContext.exceptions =
            some evidenceTargetException ∧
          (if evidenceException = "E" then some 9 else none) =
            some evidenceTargetException ∧
          panValueFlatWords evidenceValue = values ∧
          List.Pairwise (fun left right : Nat => left ≠ right)
            (storeAddresses 0 evidenceContext.bytesInWord values.length) ∧
          Shape.shapeSize (panValueShape evidenceStructs evidenceValue) ≤ 32 := by
    intro evidenceContext evidenceStructs evidenceExceptionRel
      evidenceLocals evidenceGlobals evidenceMemory evidenceException evidenceValue
      evidenceTargetState evidenceTargetException hcontrol
    rcases hevidence evidenceContext evidenceStructs evidenceExceptionRel
      evidenceLocals evidenceGlobals evidenceMemory evidenceException evidenceValue
      evidenceTargetState evidenceTargetException hcontrol with
      ⟨evidenceState, expression, compiled, shape, htarget, hbytesInWord,
        hrel, hsource, hvalid, hcompile, hlength, hcompiled, hnot, hfresh,
        hexception, hlookupCode, hcode, hdistinct, hsize⟩
    exact ⟨evidenceState, expression, compiled, shape,
      panValueFlatWords evidenceValue, htarget, hbytesInWord, hrel, hsource,
      hvalid, hcompile, hlength, hcompiled, hnot, hfresh, hexception,
      hlookupCode, hcode, rfl, hdistinct, hsize⟩
  have hresult :=
    panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_context_code_and_clocked_control
      (.raise "E" sourceExpression)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] []
      (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 8 sourceFuel targetFuel hprogram hprogramSafe (by
        intro targetState sourceValue
        rfl) hevidenceWithValues
        [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
      directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi .skip (.normal state)
      (.normal (fun _ => none) (fun _ => none) (fun _ => none))
      (.normal state) hclock hclockState (by simp [panValuePcControlLabelSafe]) (by rfl)
      (by
        intro sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue targetState targetException hcontrol
        exact panValuePcClockedRaisedResultRel_of_flat_global_evaluator_evidence
          (α := Nat) [] context (fun _ _ code => code = 9)
          (fun exception => if exception = "E" then some 9 else none)
          (crepPcFlatGlobalsLookup 8) [] []
          (fun _ _ => none) (fun _ _ _ _ _ _ => none)
          (fun _ _ => none) (fun _ _ _ _ _ _ => none)
          (fun _ _ _ _ => none) 0 0 8 2 (by
            intro targetState sourceValue
            rfl) hevidenceWithValues sourceLocals sourceGlobals sourceMemory
          sourceException sourceValue targetState targetException hcontrol)
  refine ⟨hresult.1, ?_, ?_⟩
  · exact hclock
  · simp [panValuePcResultRelWithContextCode, panValuePcResultRel,
      hclockState]

theorem three_word_raise_pc_compile_correct_direct_clocked_raised
    (sourceFuel targetFuel : Nat)
    (targetState : CrepState Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
        0 0 targetFuel)
      (fun _ _ _ => True)
      (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raise "E" sourceExpression))
    (hclock :
      evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" sourceValue), 1))
    (hclockState : panValueCrepStateRel [] context
      (fun _ => none) (fun _ => none) (fun _ => none) targetState)
    (hclockRaiseData : panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      targetState 9 ∧
      lookupInfo "E" context.exceptions = some 9) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
        0 0 targetFuel)
      (fun _ _ _ => True)
      (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raise "E" sourceExpression) ∧
    evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" sourceValue), 1) ∧
    (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression)).map
        panValueFfiClockResultProjection =
      some (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" sourceValue 1) ∧
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" sourceValue)
      (.raised targetState 9) := by
  have hordinaryCompact := panValuePcCompileCorrect_of_context_code
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression) hcompact
  have _hordinary :=
    panValuePcCompileCorrect_of_compact_evaluators_and_clocked_raised_hraise_data
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression)
      hordinaryCompact [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
      directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi (.raise "E" sourceExpression)
      targetState "E" sourceValue 9 hclock hclockState hclockRaiseData.1
  exact panValuePcCompileCorrectWithContextCode_of_compact_evaluators_and_clocked_raised_hraise_data
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression)
    hcompact [] context (fun _ _ code => code = 9)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
    directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
    (fun _ => none) directClockFfi (.raise "E" sourceExpression)
    targetState "E" sourceValue 9 hclock hclockState hclockRaiseData

theorem nested_raise_pc_compile_correct_direct_clocked_raised
    (sourceFuel targetFuel : Nat)
    (targetState : CrepState Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
        0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" nestedSourceExpression))
    (hclock :
      evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" nestedSourceValue), 1))
    (hclockState : panValueCrepStateRel [] context
      (fun _ => none) (fun _ => none) (fun _ => none) targetState)
    (hclockRaiseData : panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) [] context (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" nestedSourceValue
      targetState 9 ∧ lookupInfo "E" context.exceptions = some 9) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" nestedSourceExpression) ∧
    evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" nestedSourceValue), 1) ∧
    (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression)).map
        panValueFfiClockResultProjection =
      some (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" nestedSourceValue 1) ∧
    panValuePcResultRelWithContextCode [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" nestedSourceValue) (.raised targetState 9) := by
  exact panValuePcCompileCorrectWithContextCode_of_compact_evaluators_and_clocked_raised_hraise_data
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) (.raise "E" nestedSourceExpression)
    hcompact [] context (fun _ _ code => code = 9)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
    directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
    (fun _ => none) directClockFfi (.raise "E" nestedSourceExpression)
    targetState "E" nestedSourceValue 9 hclock hclockState hclockRaiseData

theorem nested_raise_pc_compile_correct_direct_clocked_raised_projection
    (sourceFuel targetFuel : Nat)
    (targetState : CrepState Nat)
    (hcontext :
      PanValuePcCompileCorrectWithContextCode
        (panValuePcCompactSourceEvaluator
          (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
        (crepPcCompactTargetEvaluator [] (fun _ _ => none)
          (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
          0 0 targetFuel)
        (fun _ _ _ => True) (fun _ _ _ => True)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcFlatGlobalsLookup 8) (.raise "E" nestedSourceExpression) ∧
      evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression) =
        some (.control (.raised (fun _ => none) (fun _ => none)
          (fun _ => none) directClockFfi "E" nestedSourceValue), 1) ∧
      (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression)).map
          panValueFfiClockResultProjection =
        some (.raised (fun _ => none) (fun _ => none)
          (fun _ => none) directClockFfi "E" nestedSourceValue 1) ∧
      panValuePcResultRelWithContextCode [] context
        (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcFlatGlobalsLookup 8)
        (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" nestedSourceValue) (.raised targetState 9)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
        0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" nestedSourceExpression) ∧
    evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" nestedSourceValue), 1) ∧
    (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" nestedSourceExpression)).map
        panValueFfiClockResultProjection =
      some (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" nestedSourceValue 1) ∧
    panValuePcResultRel [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" nestedSourceValue) (.raised targetState 9) := by
  exact panValuePcCompileCorrect_of_context_code_and_clocked_raised
    (.raise "E" nestedSourceExpression)
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8)
    hcontext.1 [] context (fun _ _ code => code = 9)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
    directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
    (fun _ => none) directClockFfi (.raise "E" nestedSourceExpression)
    targetState "E" nestedSourceValue 9 hcontext.2.1 hcontext.2.2.2.1
    hcontext.2.2.2.2

example
    (sourceFunctions : List (FunName × List VarName × Prog Nat))
    (functions : List (CompiledFunction Nat))
    (primitive : PanPrimitiveHandler Nat)
    (sourceHandler : PanValueFfiHandler Nat)
    (crepPrimitive : CrepPrimitiveHandler Nat)
    (ffi : CrepFfiHandler Nat)
    (sharedMem : CrepSharedMemHandler Nat)
    (baseAddress topAddress bytesInWord sourceFuel targetFuel : Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler Nat)
      (ffi : CrepFfiHandler Nat), panValueCrepExtCallCorrect sourceHandler ffi)
    (hraiseData : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength)) := by
  exact panValuePcCompileCorrect_compact_extCall_const
    sourceFunctions functions primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel codeRel excpRel
    exceptionCode globalsLookup function configuration configurationLength array
    arrayLength hffi hraiseData

example
    (sourceFunctions : List (FunName × List VarName × Prog Nat))
    (functions : List (CompiledFunction Nat))
    (primitive : PanPrimitiveHandler Nat)
    (sourceHandler : PanValueFfiHandler Nat)
    (crepPrimitive : CrepPrimitiveHandler Nat)
    (ffi : CrepFfiHandler Nat)
    (sharedMem : CrepSharedMemHandler Nat)
    (baseAddress topAddress bytesInWord sourceFuel targetFuel : Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler Nat)
      (ffi : CrepFfiHandler Nat), panValueCrepExtCallCorrect sourceHandler ffi)
    (hraiseEvidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength)) := by
  exact panValuePcCompileCorrectWithContextCode_compact_extCall_const
    sourceFunctions functions primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel codeRel excpRel
    exceptionCode globalsLookup function configuration configurationLength array
    arrayLength hffi hraiseEvidence

example
    (oldValue : Option (PanValue Nat)) (state : CrepState Nat)
    (name : VarName) (names : List Nat)
    (sourceResult : PanValueControlResult Nat)
    (crepResult : CrepControlResult Nat)
    (hsafe : panValuePcControlLabelSafe sourceResult crepResult) :
    panValuePcControlLabelSafe
      (restorePanValueControlLocal name oldValue sourceResult)
      (restoreCrepResultList state.locals names crepResult) := by
  exact panValuePcControlLabelSafe_restore_declaration
    oldValue state name names sourceResult crepResult hsafe

example
    (context : CompileContext Nat) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog Nat))
    (functions : List (CompiledFunction Nat))
    (sourceLocals : VarName → Option (PanValue Nat))
    (sourceCalleeGlobals : VarName → Option (PanValue Nat))
    (sourceCalleeMemory : Nat → Option (PanValue Nat))
    (state callState : CrepState Nat)
    (primitive : PanPrimitiveHandler Nat)
    (sourceHandler : PanValueFfiHandler Nat)
    (crepPrimitive : CrepPrimitiveHandler Nat)
    (ffi : CrepFfiHandler Nat) (sharedMem : CrepSharedMemHandler Nat)
    (baseAddress topAddress bytesInWord : Nat)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (shape : Shape) (body : Prog Nat)
    (sourceValue : PanValue Nat)
    (sourceResult : PanValueControlResult Nat)
    (crepResult : CrepControlResult Nat)
    (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (hbody : PanValueCrepProgramStateControlSafe body)
    (hrelBody : panValueCrepStateRel structs
      { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory callState)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body = some sourceResult)
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) callState
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult) :
    panValuePcControlLabelSafe
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  exact panValueCrepDecCallControlSafe_of_body_safe
    context structs sourceFunctions functions sourceLocals
    sourceCalleeGlobals sourceCalleeMemory state callState primitive
    sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    sourceFuel targetFuel name shape body sourceValue sourceResult crepResult
    exceptionRel hbody hrelBody hsourceBody hcrepBody

example
    (sourceFuel targetFuel : Nat) (targetState : CrepState Nat)
    (hcontext :
      PanValuePcCompileCorrectWithContextCode
        (panValuePcCompactSourceEvaluator
          (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
        (crepPcCompactTargetEvaluator [] (fun _ _ => none)
          (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
        (fun _ _ _ => True) (fun _ _ _ => True)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression) ∧
      evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression) =
        some (.control (.raised (fun _ => none) (fun _ => none)
          (fun _ => none) directClockFfi "E" sourceValue), 1) ∧
      (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
        directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression)).map
          panValueFfiClockResultProjection =
        some (.raised (fun _ => none) (fun _ => none)
          (fun _ => none) directClockFfi "E" sourceValue 1) ∧
      panValuePcResultRelWithContextCode [] context
        (fun _ _ code => code = 9)
        (fun exception => if exception = "E" then some 9 else none)
        (crepPcFlatGlobalsLookup 8)
        (.raised (fun _ => none) (fun _ => none) (fun _ => none)
          "E" sourceValue)
        (.raised targetState 9)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression) ∧
    evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression) =
      some (.control (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" sourceValue), 1) ∧
    (evalPanValueFfiClockProg directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi 1 (.raise "E" sourceExpression)).map
        panValueFfiClockResultProjection =
      some (.raised (fun _ => none) (fun _ => none)
        (fun _ => none) directClockFfi "E" sourceValue 1) ∧
    panValuePcResultRel [] context
      (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" sourceValue) (.raised targetState 9) := by
  exact panValuePcCompileCorrect_compact_with_generalized_clocked_raised_context_projection
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression)
    [] context (fun _ _ code => code = 9)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
    directClockHandler [] 0 0 8 0 1 (fun _ => none) (fun _ => none)
    (fun _ => none) directClockFfi (.raise "E" sourceExpression)
    (.raised targetState 9) "E" sourceValue hcontext

example
    (hexpression : PanValueCrepExpressionStateCorrect nestedSourceExpression)
    (hnot : ∀ (compiled : List (CrepExp Nat)),
      ∀ name ∈ freshNames context compiled.length 1,
        ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ (compiled : List (CrepExp Nat)),
      ∀ name ∈ freshNames context compiled.length 1,
        state.locals name = none) :
    ∃ (compiled : List (CrepExp Nat)) (shape : Shape) (values : List Nat),
      panValuePayloadWithinLimit [] nestedSourceValue = true ∧
      compileExp context nestedSourceExpression = (compiled, shape) ∧
      compiled.length = Shape.shapeSize shape ∧
      evalCrepFullExpsState state 0 0 compiled = some values ∧
      (∀ name ∈ freshNames context compiled.length 1,
        ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
      (∀ name ∈ freshNames context compiled.length 1,
        state.locals name = none) ∧
      panValueFlatWords nestedSourceValue = values := by
  apply panValueCrepExpressionStateEvidence_of_correct
    nestedSourceExpression hexpression context [] (fun _ => none)
    (fun _ => none) (fun _ => none) state 0 0 8 nestedSourceValue
  · refine ⟨rfl, ?_, rfl⟩
    exact panValueCrepLocalsRel_empty [] context state.locals
  · simp [nestedSourceExpression, nestedSourceValue, evalPanValueExp,
      evalPanValueExp.evalPanValueExps]
  · exact hnot
  · exact hfresh
  · simp [nestedSourceValue, panValueFlatWords, panValueFlatWordsFuel,
      panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel,
      panValueShape, Shape.shapeSize]

example
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (hlookup : ∀ (targetState : CrepState Nat) (sourceValue : PanValue Nat),
      crepPcFlatGlobalsLookup 8 targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState Nat) (expression : Exp Nat),
        targetState =
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                (panValueFlatWords sourceValue)) } ∧
        context.bytesInWord = 8 ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        PanValueCrepExpressionStateCorrect expression ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          0 0 8 expression = some sourceValue ∧
        (∀ (compiled : List (CrepExp Nat)),
          ∀ name ∈ freshNames context compiled.length 1,
            ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ (compiled : List (CrepExp Nat)),
          ∀ name ∈ freshNames context compiled.length 1,
            state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        exceptionCode sourceException = some targetException ∧
        List.Pairwise (fun left right : Nat => left ≠ right)
          (storeAddresses 0 context.bytesInWord
            (panValueFlatWords sourceValue).length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32 ∧
        (panValueFlatWords sourceValue).length =
          Shape.shapeSize (panValueShape structs sourceValue)) :
    True := by
  have hbridge := panValuePcRaisedHraiseData_of_expression_state_evidence
    exceptionCode globalsLookup [] [] (fun _ _ => none)
    (fun _ _ _ _ _ _ => none) (fun _ _ => none)
    (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 8 0 hlookup hevidence
  trivial

example
    (sourceFuel targetFuel : Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression))
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (event targetEvent : FfiFinalEvent) (finalFfi : FfiState Unit)
    (hclock : evalPanValueFfiClockLeaf directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi clockProgram =
      some (.control
        (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
          finalFfi event), 1))
    (hclockState : panValueCrepStateRel [] context
      (fun _ => none) (fun _ => none) (fun _ => none) clockTargetState)
    (hevent : event = targetEvent) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
      (crepPcCompactTargetEvaluator [] (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
      (fun _ _ _ => True) (fun _ _ _ => True)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression) ∧
    evalPanValueFfiClockLeaf directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi clockProgram =
      some (.control
        (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
          finalFfi event), 1) ∧
    (evalPanValueFfiClockLeaf directClockContext (fun _ _ => none)
      directClockHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) directClockFfi clockProgram).map
        panValueFfiClockResultProjection =
      some (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
        finalFfi event 1) ∧
    panValuePcResultRelWithContextCode [] context (fun _ _ code => code = 9)
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcFlatGlobalsLookup 8)
      (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none) event)
      (.finalFfi clockTargetState targetEvent) := by
  exact panValuePcCompileCorrectWithContextCode_of_compact_evaluators_and_clocked_final_ffi
    (panValuePcCompactSourceEvaluator
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] 0 0 8 sourceFuel)
    (crepPcCompactTargetEvaluator [] (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 targetFuel)
    (fun _ _ _ => True) (fun _ _ _ => True)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) (.raise "E" sourceExpression) hcompact [] context
    (fun _ _ code => code = 9)
    (fun exception => if exception = "E" then some 9 else none)
    (crepPcFlatGlobalsLookup 8) directClockContext (fun _ _ => none)
    directClockHandler [] 0 0 8 1 (fun _ => none) (fun _ => none)
    (fun _ => none) directClockFfi clockProgram clockTargetState event
    targetEvent finalFfi hclock hclockState hevent

def runChecks : IO Bool := do
  IO.println "PASS generic three-word Raise evaluator relation"
  IO.println "PASS context-coded clock evidence projects to semantic outcome relation"
  IO.println "PASS generic raised semantic/global lookup lift"
  IO.println "PASS direct arbitrary context-coded pc_compile_correct evaluator instantiation"
  IO.println "PASS direct arbitrary context-coded clocked evaluator instantiation"
  IO.println "PASS direct arbitrary context-coded raised clock evaluator instantiation"
  IO.println "PASS nested arbitrary context-coded clocked Raise projects to pc_compile_correct"
  IO.println "PASS compact ExtCall pc_compile_correct bridge instantiation"
  IO.println "PASS compact ExtCall context-coded bridge instantiation"
  IO.println "PASS declaration restoration preserves control-label safety"
  IO.println "PASS DecCall body control safety survives caller restoration"
  IO.println "PASS generic clocked Raise projects to pc_compile_correct"
  IO.println "PASS ordinary clocked Raise consumes explicit hraise data"
  IO.println "PASS expression-state contract packages generic Raise evidence"
  IO.println "PASS expression-state evidence derives generic flat-global Raise package"
  IO.println "PASS expression-state evidence composes to compact pc_compile_correct"
  IO.println "PASS expression-state evidence composes to context-coded pc_compile_correct"
  IO.println "PASS expression-state context bridge composes with clocked Raise"
  IO.println "PASS expression-state ordinary bridge composes with clocked Raise"
  IO.println "PASS expression-state context bridge composes with clocked Timeout"
  IO.println "PASS expression-state ordinary bridge composes with clocked Timeout"
  IO.println "PASS compact context bridge composes with clocked FinalFFI"
  IO.println "PASS expression-state ordinary bridge composes with clocked FinalFFI"
  IO.println "PASS expression-state evidence supplies generic Raise fallback"
  IO.println "PASS expression-state evidence composes to clocked Returned"
  IO.println "PASS expression-state evidence composes to clocked Normal"
  IO.println "PASS expression-state evidence composes to generic clocked control"
  IO.println "PASS expression-state evidence derives ordinary Raise result relation"
  IO.println "PASS compact correctness composes with generic clocked control"
  IO.println "PASS expression-state evidence derives context-coded Raise result relation"
  IO.println "PASS expression-state evidence discharges arbitrary context-coded clocked control"
  IO.println "PASS expression-state evidence discharges arbitrary context-coded clocked Raise"
  IO.println "PASS expression-state evidence discharges arbitrary ordinary clocked control"
  IO.println "PASS expression-state evidence discharges arbitrary ordinary clocked Raise"
  IO.println "PASS arbitrary ordinary clocked Timeout preserves state relation"
  IO.println "PASS arbitrary ordinary clocked FinalFFI preserves event relation"
  IO.println "PASS arbitrary ordinary clocked Returned preserves values relation"
  IO.println "PASS arbitrary ordinary clocked Normal preserves state relation"
  IO.println "PASS arbitrary ordinary clocked Broke preserves label zero"
  IO.println "PASS arbitrary ordinary clocked Continued preserves label zero"
  IO.println "PASS nested raised semantic/global lookup lift"
  pure true

end Flapjack.Test.CrepeProgramGenericRaiseCorrectness
