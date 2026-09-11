import Flapjack.CrepeSourceWordGenericStoreCorrectness

namespace Flapjack

def sourceWordGenericStoreContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordGenericStoreState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_generic_store_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 4 sourceWordGenericStoreState
        (compileProg sourceWordGenericStoreContext
          (.store (SourceWordExp.const (4 : Nat)).toExp
            (SourceWordExp.const 7).toExp)) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordGenericStoreContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordGenericStoreState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordGenericStoreContext _, ?_⟩
    funext address
    simp [panValueWordMemory, sourceWordGenericStoreState]
  have h := compile_full_pan_value_store_source_word_relation (α := Nat)
    (context := sourceWordGenericStoreContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordGenericStoreState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (address := .const 4) (value := .const 7)
    (addressValue := 4) (valueValue := 7) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsourceValue := by simp [SourceWordExp.toExp, evalPanValueExp])
    (haddressStable := by
      intro compiled hcompile
      simp [SourceWordExp.toExp, compileExp] at hcompile
      subst compiled
      simp [evalCrepFullExp])
    (hvalueStable := by
      intro compiled hcompile
      simp [SourceWordExp.toExp, compileExp] at hcompile
      subst compiled
      simp [evalCrepFullExp])
  exact ⟨_, h.2.1⟩

end Flapjack
