import Flapjack.CrepeSourceWordRecordRaiseCorrectness

namespace Flapjack

def sourceWordRecordRaiseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 8 }

def sourceWordRecordRaiseState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_record_raise_relation :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 15 sourceWordRecordRaiseState
        (compileProg sourceWordRecordRaiseContext
          (.raise "E" (.rStruct
            [(SourceWordExp.const (3 : Nat)).toExp,
              (SourceWordExp.const 4).toExp]))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordRecordRaiseContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordRecordRaiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordRecordRaiseContext _, rfl⟩
  have h := compile_full_pan_value_raise_source_word_two_fields_relation
    (α := Nat) (context := sourceWordRecordRaiseContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordRecordRaiseState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (fieldLeft := .const 3) (fieldRight := .const 4) (left := 3) (right := 4)
    (exception := "E") (exceptionCode := 9)
    (exceptionRel := fun _ _ code => code = 9)
    (compiledLeft := .const 3) (compiledRight := .const 4)
    (hlookup := by simp [sourceWordRecordRaiseContext, lookupInfo])
    (hbytesInWord := rfl) (hrel := hrel)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp,
        evalPanValueExp.evalPanValueExps])
    (hcompile := by simp [SourceWordExp.toExp, compileExp,
      compileExp.compileExpList])
    (hcompiledLeft := by simp [evalCrepFullExp])
    (hcompiledRight := by
      intro value
      simp [evalCrepFullExp])
    (hexception := by simp)
  exact ⟨_, h.2.1⟩

end Flapjack
