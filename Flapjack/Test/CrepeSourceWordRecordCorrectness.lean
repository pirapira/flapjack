import Flapjack.CrepeSourceWordRecordCorrectness

namespace Flapjack

def sourceWordRecordContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordRecordState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_record_return_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 1 sourceWordRecordState
        (compileProg sourceWordRecordContext
          (.return (.rStruct
            [(SourceWordExp.const (3 : Nat)).toExp,
              (SourceWordExp.const 4).toExp]))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordRecordContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordRecordState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordRecordContext _, ?_⟩
    funext address
    simp [panValueWordMemory, sourceWordRecordState]
  have h := compile_full_pan_value_return_record_source_word_relation (α := Nat)
    (context := sourceWordRecordContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordRecordState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (fields := [.const 3, .const 4]) (values := [3, 4]) (exceptionRel := fun _ _ _ => True)
    (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hvalid := by
      simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
        panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel])
  exact ⟨_, h.2.1⟩

end Flapjack
