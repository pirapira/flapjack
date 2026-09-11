import Flapjack.CrepeSourceWordStoreByteLoadCorrectness

namespace Flapjack

def sourceWordStoreByteLoadContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordStoreByteLoadState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_storeByte_load_one_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 2 sourceWordStoreByteLoadState
        (compileProg sourceWordStoreByteLoadContext
          (.seq
            (.storeByte (SourceWordExp.const (4 : Nat)).toExp
              (SourceWordExp.const 7).toExp)
            (.return (.load .one (SourceWordExp.const (4 : Nat)).toExp)))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordStoreByteLoadContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordStoreByteLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordStoreByteLoadContext _, ?_⟩
    funext address
    simp [panValueWordMemory, sourceWordStoreByteLoadState]
  have h := compile_full_pan_value_storeByte_load_one_source_word_relation (α := Nat)
    (context := sourceWordStoreByteLoadContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordStoreByteLoadState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (storeAddress := .const 4) (storeValue := .const 7)
    (loadAddress := .const 4) (storeAddressValue := 4)
    (storeValueValue := 7) (loadAddressValue := 4) (loadValue := 7)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hstoreAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hstoreValue := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hloadAddress := by
      simp [SourceWordExp.toExp, evalPanValueExp, updatePanValueMemory])
    (hload := by
      simp [SourceWordExp.toExp, evalPanValueExp, updatePanValueMemory,
        updatePanValueMap, panValueFlatLoad, panValueFlatLoadFuel,
        panValueFlatReadWord, isWfShape])
  exact ⟨_, h.2.1⟩

end Flapjack
