import Flapjack.CrepeProgramGenericRaiseCorrectness
import Flapjack.PanToCrepCorrectnessBridge

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

def runChecks : IO Bool := do
  IO.println "PASS generic three-word Raise evaluator relation"
  pure true

end Flapjack.Test.CrepeProgramGenericRaiseCorrectness
