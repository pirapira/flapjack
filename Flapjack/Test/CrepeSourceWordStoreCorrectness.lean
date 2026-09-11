import Flapjack.CrepeSourceWordStoreCorrectness

namespace Flapjack

def sourceWordStoreContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordStoreState : CrepState Nat :=
  { locals := fun _ => none, memory := fun address => if address = 4 then some 1 else none }

theorem closed_source_word_store32_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 2 sourceWordStoreState
        (compileProg sourceWordStoreContext
          (.store32 (SourceWordExp.const (4 : Nat)).toExp
            (SourceWordExp.const 7).toExp)) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordStoreContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordStoreState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordStoreContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordStoreState, haddress]
  have h := compile_full_pan_value_store32_source_word_relation (α := Nat)
    (context := sourceWordStoreContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none)
    (sourceMemory := fun address => if address = 4 then some (.word 1) else none)
    (state := sourceWordStoreState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8) (fuel := 1)
    (address := .const 4) (value := .const 7) (addressValue := 4) (valueValue := 7)
    (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsourceValue := by simp [SourceWordExp.toExp, evalPanValueExp])
  rcases h.2 with ⟨compiledAddress, compiledValue, hcompileAddress,
    hcompileValue, hprogram, hpost⟩
  exact ⟨_, hprogram⟩

end Flapjack
