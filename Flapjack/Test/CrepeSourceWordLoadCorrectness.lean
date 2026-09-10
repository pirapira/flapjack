import Flapjack.CrepeSourceWordLoadCorrectness

namespace Flapjack

def sourceWordLoadContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordLoadState : CrepState Nat :=
  { locals := fun _ => none,
    memory := fun address => if address = 4 then some 1 else none }

theorem closed_source_word_load_one_bridge :
    ∃ compiled,
      compileExp sourceWordLoadContext
          (.load .one (SourceWordExp.const (4 : Nat)).toExp) =
        ([compiled], .one) ∧
      evalCrepFullExp sourceWordLoadState.locals sourceWordLoadState.memory
          0 0 compiled = some 1 := by
  have hrel : panValueCrepStateRel [] sourceWordLoadContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordLoadContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordLoadState, haddress]
  exact compileSourceWord_load_one_relation (α := Nat)
    (context := sourceWordLoadContext) (structs := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordLoadState) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (address := .const 4) (addressValue := 4) (value := 1)
    (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp, panValueFlatLoad,
        panValueFlatLoadFuel, panValueFlatReadWord, isWfShape])

theorem closed_source_word_load32_bridge :
    ∃ compiled,
      compileExp sourceWordLoadContext
          (.load32 (SourceWordExp.const (4 : Nat)).toExp) =
        ([compiled], .one) ∧
      evalCrepFullExp sourceWordLoadState.locals sourceWordLoadState.memory
          0 0 compiled = some 1 := by
  have hrel : panValueCrepStateRel [] sourceWordLoadContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordLoadContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordLoadState, haddress]
  exact compileSourceWord_load32_relation (α := Nat)
    (context := sourceWordLoadContext) (structs := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordLoadState) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (address := .const 4) (addressValue := 4) (value := 1)
    (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])

theorem closed_source_word_loadByte_bridge :
    ∃ compiled,
      compileExp sourceWordLoadContext
          (.loadByte (SourceWordExp.const (4 : Nat)).toExp) =
        ([compiled], .one) ∧
      evalCrepFullExp sourceWordLoadState.locals sourceWordLoadState.memory
          0 0 compiled = some 1 := by
  have hrel : panValueCrepStateRel [] sourceWordLoadContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordLoadContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordLoadState, haddress]
  exact compileSourceWord_loadByte_relation (α := Nat)
    (context := sourceWordLoadContext) (structs := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordLoadState) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (address := .const 4) (addressValue := 4) (value := 1)
    (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])

end Flapjack
