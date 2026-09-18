import Flapjack.PanToCrepCorrectnessBridge

namespace Flapjack.Test.PanValuePcRaisedPayloadCorrectness

open Flapjack

def raiseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 8 }

def raiseState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

def raiseResultExceptionCode : ExceptionId → Option Nat
  | "E" => some 9
  | _ => none

def raiseWordGlobalsLookup (_state : CrepState Nat) (value : PanValue Nat) :
    Option (List Nat) :=
  some (panValueFlatWords value)

theorem pc_break_requires_zero_label :
    ¬ panValuePcResultRel [] raiseContext (fun _ _ code => code = 9)
      raiseResultExceptionCode raiseWordGlobalsLookup
      (.broke (fun _ => none) (fun _ => none) (fun _ => none))
      (.broke raiseState 1) := by
  simp [panValuePcResultRel]

theorem pc_continue_requires_zero_label :
    ¬ panValuePcResultRel [] raiseContext (fun _ _ code => code = 9)
      raiseResultExceptionCode raiseWordGlobalsLookup
      (.continued (fun _ => none) (fun _ => none) (fun _ => none))
      (.continued raiseState 1) := by
  simp [panValuePcResultRel]

theorem pc_break_zero_label_preserves_state :
    panValuePcResultRel [] raiseContext (fun _ _ code => code = 9)
      raiseResultExceptionCode raiseWordGlobalsLookup
      (.broke (fun _ => none) (fun _ => none) (fun _ => none))
      (.broke raiseState 0) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  simpa [panValuePcResultRel] using hstate

/-! A closed source raise supplies the concrete semantic premises needed by the
    Pc raised-result obligation.  In particular, the conclusion retains the
    post-state relation, exception-code lookup, and the flattened global
    payload observation rather than treating the raised branch as opaque. -/
theorem closed_word_raise_pc_hraise :
    (panValueCrepStateRel [] raiseContext (fun _ => none) (fun _ => none)
        (fun _ => none) raiseState ∧
      (∃ spillAddress,
        panValueCrepRaisedControlRel [] raiseContext
          (fun _ _ code => code = 9) (fun _ => none) (fun _ => none)
          "E" (.word 3)
          { raiseState with globals := updateMemory raiseState.globals 0 3 }
          9 spillAddress ∧
        raiseResultExceptionCode "E" = some 9 ∧
        (1 ≤ Shape.shapeSize (panValueShape [] (.word 3)) →
          crepPcWordGlobalsLookup
            { raiseState with globals := updateMemory raiseState.globals 0 3 }
            (.word 3) = some (panValueFlatWords (.word 3))) ∧
        Shape.shapeSize (panValueShape [] (.word 3)) ≤ 32)) ∧
      lookupInfo "E" raiseContext.exceptions = some 9 := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  have h := panValuePcRaisedWordHraise
    (α := Nat) (context := raiseContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := raiseState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (targetFuel := 2) (exception := "E")
    (exceptionCode := 9) (value := 3) (expression := .const 3)
    (compiled := .const 3)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := raiseResultExceptionCode)
    (hlookup := by simp [raiseContext, lookupInfo])
    (hcode := by simp [raiseResultExceptionCode])
    (hbytesInWord := rfl) (hrel := hstate)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp])
    (hcompile := by simp [SourceWordExp.toExp, compileExp])
    (hcompiled := by simp [evalCrepFullExpState, raiseState])
    (hexception := by simp)
    (hfresh := by simp [raiseState, raiseContext])
  exact ⟨h.1, h.2⟩

theorem closed_word_raise_pc_hraise_flat_globals :
    panValuePcRaisedHraiseData raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8) [] raiseContext
      (fun _ _ code => code = 9) (fun _ => none) (fun _ => none)
      (fun _ => none) "E" (.word 3)
      { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  apply panValuePcRaisedHraiseData_retarget_globals_lookup
    (bytesInWord := 8) (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := crepPcFlatGlobalsLookup 8)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := .word 3)
    (targetState :=
      { raiseState with globals := updateMemory raiseState.globals 0 3 })
    (targetException := 9)
  · simp [crepPcFlatGlobalsLookup, panValueFlatWords, panValueFlatWordsFuel]
  · exact closed_word_raise_pc_hraise.1

theorem closed_word_raise_pc_result_rel_flat_globals :
    panValuePcResultRel [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" (.word 3))
      (.raised { raiseState with globals := updateMemory raiseState.globals 0 3 }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := crepPcFlatGlobalsLookup 8)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := .word 3)
    (targetState :=
      { raiseState with globals := updateMemory raiseState.globals 0 3 })
    (targetException := 9)
  exact closed_word_raise_pc_hraise_flat_globals

theorem closed_word_raise_pc_result_rel_with_context_code_preserves_source_locals :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcWordGlobalsLookup (α := Nat))
      (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        "E" (.word 3))
      (.raised { raiseState with globals := updateMemory raiseState.globals 0 3 }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => some (.word 7)) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  apply panValuePcResultRelWithContextCode_of_raised_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (value := 3) (state := raiseState)
    (targetException := 9) (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo])

/-! The strict raised-result relation rejects a result code that is supplied by
    an unrelated adapter map rather than by the source compiler context. -/
def mismatchedRaiseContext : CompileContext Nat :=
  { raiseContext with exceptions := [("E", 10)] }

theorem pc_raised_result_requires_context_exception_code :
    ¬ panValuePcExceptionResultRelWithContextCode [] mismatchedRaiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      raiseWordGlobalsLookup (fun _ => none) (fun _ => none)
      "E" (.word 3) { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  simp [panValuePcExceptionResultRelWithContextCode, mismatchedRaiseContext,
    raiseContext, lookupInfo]

theorem closed_two_word_raise_pc_hraise_flat_globals :
    (panValuePcRaisedHraiseData raiseResultExceptionCode
        (crepPcFlatGlobalsLookup 8) [] raiseContext
        (fun _ _ code => code = 9) (fun _ => none) (fun _ => none)
        (fun _ => none) "E" (.rStruct [.word 3, .word 4])
        { raiseState with globals :=
            (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
        9) ∧
      lookupInfo "E" raiseContext.exceptions = some 9 := by
  have h := panValuePcRaisedTwoWordHraise
    (α := Nat) (context := raiseContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := raiseState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (fieldLeft := .const 3) (fieldRight := .const 4)
    (left := 3) (right := 4) (exception := "E") (exceptionCode := 9)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := raiseResultExceptionCode)
    (compiledLeft := .const 3) (compiledRight := .const 4)
    (hlookup := by simp [raiseContext, lookupInfo])
    (hcode := by simp [raiseResultExceptionCode])
    (hbytesInWord := rfl) (hdistinct := by decide)
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hcompile := by
      simp [SourceWordExp.toExp, compileExp, compileExp.compileExpList])
    (hcompiledLeft := by
      simp [evalCrepFullExpState, raiseState])
    (hcompiledRight := by
      intro value
      simp [evalCrepFullExpState, raiseState])
    (hexception := by simp)
  have htwoData := h.1
  rcases htwoData with ⟨hpost, spillAddress, hcontrol, hcode, hpayload, hsize⟩
  refine ⟨?_, h.2⟩
  refine ⟨hpost, spillAddress, hcontrol, hcode, ?_, hsize⟩
  intro _
  have hlookup :
      crepPcTwoWordGlobalsLookup 8
          { raiseState with globals :=
              (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
          (.rStruct [.word 3, .word 4]) =
        crepPcFlatGlobalsLookup 8
          { raiseState with globals :=
              (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
          (.rStruct [.word 3, .word 4]) := by
    have htwo :
        crepPcTwoWordGlobalsLookup 8
            { raiseState with globals :=
                (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
            (.rStruct [.word 3, .word 4]) = some [3, 4] := by
      simp [crepPcTwoWordGlobalsLookup, updateMemory]
    have hflat := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 raiseState (.rStruct [.word 3, .word 4]) (by decide)
    have hflat' :
        crepPcFlatGlobalsLookup 8
            { raiseState with globals :=
                (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
            (.rStruct [.word 3, .word 4]) = some [3, 4] := by
      simpa [crepPcFlatGlobalsLookup, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel, updateMemoryListAt,
        Nat.zero_add] using hflat
    exact htwo.trans hflat'.symm
  rw [← hlookup]
  simpa [Nat.zero_add] using
    (hpayload (by simp [panValueShape, Shape.shapeSize]))

theorem closed_two_word_raise_pc_result_rel_flat_globals :
    panValuePcResultRel [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4]))
      (.raised
        { raiseState with globals :=
            (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
        9) := by
  apply panValuePcResultRel_of_raised_hraise_data
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := crepPcFlatGlobalsLookup 8)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := .rStruct [.word 3, .word 4])
    (targetState :=
      { raiseState with globals :=
          (updateMemory (updateMemory raiseState.globals 0 3) 8 4) })
    (targetException := 9)
  exact closed_two_word_raise_pc_hraise_flat_globals.1

theorem closed_two_word_raise_pc_result_rel_with_context_code :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcTwoWordGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4]))
      (.raised
        { raiseState with globals :=
            (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  apply panValuePcResultRelWithContextCode_of_raised_two_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (bytesInWord := 8) (left := 3) (right := 4)
    (state := raiseState) (targetException := 9)
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo]) (hdistinct := by decide)

theorem closed_two_word_raise_pc_result_rel_with_context_code_preserves_source_locals :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcTwoWordGlobalsLookup 8)
      (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        "E" (.rStruct [.word 3, .word 4]))
      (.raised
        { raiseState with globals :=
            (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => some (.word 7)) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  apply panValuePcResultRelWithContextCode_of_raised_two_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (bytesInWord := 8) (left := 3) (right := 4)
    (state := raiseState) (targetException := 9)
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo]) (hdistinct := by decide)

theorem closed_word_raise_pc_result_rel_retargeted :
    panValuePcResultRel [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      raiseWordGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" (.word 3))
      (.raised { raiseState with globals := updateMemory raiseState.globals 0 3 }
        9) := by
  apply panValuePcRaisedWordResultRel_retarget_globals
    (context := raiseContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := raiseState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (targetFuel := 2) (exception := "E")
    (exceptionCode := 9) (value := 3) (expression := .const 3)
    (compiled := .const 3)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := raiseResultExceptionCode)
    (globalsLookup := raiseWordGlobalsLookup)
    (hlookup := by simp [raiseContext, lookupInfo])
    (hcode := by simp [raiseResultExceptionCode])
    (hbytesInWord := rfl)
    (hrel := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩)
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hcompile := by simp [SourceWordExp.toExp, compileExp])
    (hcompiled := by simp [evalCrepFullExpState, raiseState])
    (hexception := by simp)
    (hfresh := by simp [raiseState, raiseContext])
    (hlookupGlobals := by
      simp [raiseWordGlobalsLookup, crepPcWordGlobalsLookup,
        updateMemory, panValueFlatWords, panValueFlatWordsFuel])

theorem pc_raised_result_accepts_context_exception_code :
    panValuePcExceptionResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      raiseWordGlobalsLookup (fun _ => none) (fun _ => none)
      "E" (.word 3) { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  refine ⟨closed_word_raise_pc_result_rel_retargeted.2, ?_⟩
  simp [raiseContext, lookupInfo]

theorem closed_two_word_raise_pc_result_rel :
    panValuePcResultRel [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcTwoWordGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4]))
      (.raised
        { raiseState with globals :=
            (updateMemory (updateMemory raiseState.globals 0 3) 8 4) }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  apply panValuePcRaisedTwoWordResultRel_of_semantic_lift
    (α := Nat) (context := raiseContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := raiseState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (fieldLeft := .const 3) (fieldRight := .const 4)
    (left := 3) (right := 4) (exception := "E") (exceptionCode := 9)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := raiseResultExceptionCode)
    (compiledLeft := .const 3) (compiledRight := .const 4)
    (hlookup := by simp [raiseContext, lookupInfo])
    (hcode := by simp [raiseResultExceptionCode])
    (hbytesInWord := rfl) (hdistinct := by decide) (hrel := hstate)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hcompile := by
      simp [SourceWordExp.toExp, compileExp, compileExp.compileExpList])
    (hcompiledLeft := by
      simp [evalCrepFullExpState, raiseState])
    (hcompiledRight := by
      intro value
      simp [evalCrepFullExpState, raiseState])
    (hexception := by simp)

theorem closed_three_word_raise_pc_global_spill :
    panValuePcExceptionResultRel [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcThreeWordGlobalsLookup 8) (fun _ => none) (fun _ => none)
      "E" (.rStruct [.word 3, .word 4, .word 5])
      { raiseState with globals :=
          updateMemoryListAt raiseState.globals 0 8 [3, 4, 5] }
      9 := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  apply panValuePcExceptionResultRel_of_raised_three_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (bytesInWord := 8)
    (first := 3) (second := 4) (third := 5)
    (state := raiseState) (targetException := 9) hstate
  · rfl
  · simp [raiseResultExceptionCode]
  · decide
  · decide
  · decide

theorem closed_three_word_raise_pc_result_rel_with_context_code :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcThreeWordGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4, .word 5]))
      (.raised
        { raiseState with globals :=
            updateMemoryListAt raiseState.globals 0 8 [3, 4, 5] }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  apply panValuePcResultRelWithContextCode_of_raised_three_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (bytesInWord := 8)
    (first := 3) (second := 4) (third := 5)
    (state := raiseState) (targetException := 9)
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo])
    (hdistinct01 := by decide) (hdistinct02 := by decide)
    (hdistinct12 := by decide)

theorem closed_three_word_raise_pc_result_rel_with_context_code_preserves_source_locals :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcThreeWordGlobalsLookup 8)
      (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none)
        "E" (.rStruct [.word 3, .word 4, .word 5]))
      (.raised
        { raiseState with globals :=
            updateMemoryListAt raiseState.globals 0 8 [3, 4, 5] }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => some (.word 7)) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  apply panValuePcResultRelWithContextCode_of_raised_three_word_global_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (bytesInWord := 8)
    (first := 3) (second := 4) (third := 5)
    (state := raiseState) (targetException := 9)
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo])
    (hdistinct01 := by decide) (hdistinct02 := by decide)
    (hdistinct12 := by decide)

theorem closed_four_word_raise_pc_result_rel_with_context_code :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4, .word 5, .word 6]))
      (.raised
        { raiseState with globals :=
            (updateMemoryListAt raiseState.globals 0 8 [3, 4, 5, 6]) }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  apply panValuePcResultRelWithContextCode_of_raised_flat_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (values := [3, 4, 5, 6])
    (state := raiseState) (bytesInWord := 8) (targetException := 9)
    (sourceValue := .rStruct [.word 3, .word 4, .word 5, .word 6])
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo])
    (hflat := by
      simp [panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide) (hsize := by simp [panValueShape, Shape.shapeSize])

theorem closed_four_word_raise_pc_result_rel_with_context_code_preserves_source_locals :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8)
      (.raised (fun _ => some (.word 7)) (fun _ => none) (fun _ => none) "E"
        (.rStruct [.word 3, .word 4, .word 5, .word 6]))
      (.raised
        { raiseState with globals :=
            (updateMemoryListAt raiseState.globals 0 8 [3, 4, 5, 6]) }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => some (.word 7)) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  apply panValuePcResultRelWithContextCode_of_raised_flat_spill
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (values := [3, 4, 5, 6])
    (state := raiseState) (bytesInWord := 8) (targetException := 9)
    (sourceValue := .rStruct [.word 3, .word 4, .word 5, .word 6])
    (hstate := hstate) (hexception := by rfl)
    (hcode := by simp [raiseResultExceptionCode])
    (hlookupCode := by simp [raiseContext, lookupInfo])
    (hflat := by
      simp [panValueFlatWords, panValueFlatWordsFuel,
        panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel])
    (hdistinct := by decide) (hsize := by simp [panValueShape, Shape.shapeSize])

theorem closed_word_raise_hraise_retargeted_via_flat_spill :
    panValuePcRaisedHraiseData raiseResultExceptionCode
      raiseWordGlobalsLookup [] raiseContext
      (fun _ _ code => code = 9) (fun _ => none) (fun _ => none)
      (fun _ => none) "E" (.word 3)
      { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  apply panValuePcRaisedHraiseData_of_flat_spill_state_retarget_globals
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := raiseWordGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (values := [3]) (state := raiseState) (bytesInWord := 8)
    (targetException := 9) (sourceValue := .word 3)
  · refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  · simp
  · simp [raiseResultExceptionCode]
  · rfl
  · decide
  · simp [panValueShape]
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 raiseState (.word 3) (by decide)
    simpa [raiseWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel] using hstored

theorem closed_word_raise_hraise_retargeted_preserves_source_locals :
    panValuePcRaisedHraiseData raiseResultExceptionCode
      raiseWordGlobalsLookup [] raiseContext
      (fun _ _ code => code = 9) (fun _ => some (.word 7)) (fun _ => none)
      (fun _ => none) "E" (.word 3)
      { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  apply panValuePcRaisedHraiseData_of_flat_spill_state_retarget_globals
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := raiseWordGlobalsLookup)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (values := [3]) (state := raiseState)
    (bytesInWord := 8) (targetException := 9) (sourceValue := .word 3)
  · refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  · rfl
  · simp [raiseResultExceptionCode]
  · rfl
  · decide
  · simp [panValueShape]
  · have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
      (α := Nat) 8 raiseState (.word 3) (by decide)
    simpa [raiseWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel] using hstored

theorem closed_word_raise_hraise_flat_spill_preserves_source_locals :
    panValuePcRaisedHraiseData raiseResultExceptionCode
      (crepPcFlatGlobalsLookup 8) [] raiseContext
      (fun _ _ code => code = 9) (fun _ => some (.word 7)) (fun _ => none)
      (fun _ => none) "E" (.word 3)
      { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  apply panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (sourceLocals := fun _ => some (.word 7))
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceException := "E") (values := [3]) (state := raiseState)
    (bytesInWord := 8) (targetException := 9) (sourceValue := .word 3)
  · refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots _ hlookup
    simp [raiseContext, lookupInfo] at hlookup
  · rfl
  · simp [raiseResultExceptionCode]
  · rfl
  · decide
  · simp [panValueShape]

theorem closed_word_raise_context_code_from_hraise_data :
    panValuePcExceptionResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      raiseWordGlobalsLookup (fun _ => none) (fun _ => none)
      "E" (.word 3)
      { raiseState with globals := updateMemory raiseState.globals 0 3 }
      9 := by
  apply panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    (structs := []) (context := raiseContext)
    (exceptionRel := fun _ _ code => code = 9)
    (exceptionCode := raiseResultExceptionCode)
    (globalsLookup := raiseWordGlobalsLookup)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (sourceException := "E")
    (sourceValue := .word 3)
    (targetState :=
      { raiseState with globals := updateMemory raiseState.globals 0 3 })
    (targetException := 9) (hraiseEvidence := ?_)
  exact ⟨closed_word_raise_hraise_retargeted_via_flat_spill, by
    simp [raiseContext, lookupInfo]⟩

theorem closed_word_raise_result_context_code_relation :
    panValuePcResultRelWithContextCode [] raiseContext
      (fun _ _ code => code = 9) raiseResultExceptionCode
      raiseWordGlobalsLookup
      (.raised (fun _ => none) (fun _ => none) (fun _ => none) "E" (.word 3))
      (.raised
        { raiseState with globals := updateMemory raiseState.globals 0 3 }
        9) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { raiseState with globals := updateMemory raiseState.globals 0 3 } := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  exact ⟨hstate, closed_word_raise_context_code_from_hraise_data⟩

end Flapjack.Test.PanValuePcRaisedPayloadCorrectness
