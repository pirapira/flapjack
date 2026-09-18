import Flapjack.CrepeProgramGenericRaiseCorrectness
import Flapjack.PanToCrepCorrectnessBridge
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
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] } 9 := by
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
    panValuePcResultRel [] context (fun _ _ code => code = 9)
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

theorem three_word_raise_pc_hraise_global_spill :
    panValuePcRaisedHraiseData
      (fun exception => if exception = "E" then some 9 else none)
      (crepPcThreeWordGlobalsLookup 8) [] context
      (fun _ _ code => code = 9)
      (fun _ => none) (fun _ => none) (fun _ => none) "E" sourceValue
      { state with globals := updateMemoryListAt state.globals 0 8 [3, 4, 5] }
      9 := by
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
  apply panValuePcResultRel_of_raised_hraise_data
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
    (targetException := 9)
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
  rfl

theorem named_struct_source_pass_one_word_eval (value : Nat) :
    evalPanValueExp namedStructPassContext.structs
        (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (.nStruct "S" [("field", .const value)]) =
        some (.nStruct "S" [("field", .word value)]) ∧
    evalPanValueExp [] (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 8 (structCompileExp namedStructPassContext
          (.nStruct "S" [("field", .const value)])) =
        some (.rStruct [.word value]) := by
  simp [namedStructPassContext, structCompileExp,
    structCompileExp.structCompileFields, structSelectFields, lookupInfo,
    evalPanValueExp, evalPanValueExp.evalPanValueExps,
    evalPanValueExp.evalPanValueFields, panValueFieldsHaveShapes,
    panValueShape, panShapeMatches]

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
      9 := by
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
  · exact four_word_raise_pc_hraise_raw_words

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
  exact four_word_raise_pc_hraise_raw_words

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

def runChecks : IO Bool := do
  IO.println "PASS generic three-word Raise evaluator relation"
  pure true

end Flapjack.Test.CrepeProgramGenericRaiseCorrectness
