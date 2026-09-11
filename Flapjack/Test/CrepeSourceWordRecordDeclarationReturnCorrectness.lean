import Flapjack.CrepeSourceWordRecordDeclarationReturnCorrectness

namespace Flapjack

def sourceWordRecordDeclarationReturnContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordRecordDeclarationReturnState : CrepState Nat :=
  { locals := fun slot => if slot = 7 then some 11 else none,
    memory := fun _ => none }

theorem closed_source_word_record_declaration_return_relation :
    panValueCrepStateRel [] sourceWordRecordDeclarationReturnContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordRecordDeclarationReturnState →
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 10
        sourceWordRecordDeclarationReturnState
        (compileProg sourceWordRecordDeclarationReturnContext
          (.dec "x" (.comb [.one, .one])
            (.rStruct [.const 3, .const 4])
            (.return (.var .local "x")))) =
      some (.returned sourceWordRecordDeclarationReturnState [3, 4]) := by
  intro hrel
  exact (compile_full_pan_value_dec_two_word_record_return_relation
    (α := Nat) (context := sourceWordRecordDeclarationReturnContext)
    (structs := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordRecordDeclarationReturnState)
    (primitive := fun _ _ => none) (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none) (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (name := "x") (left := 3) (right := 4)
    (hempty := rfl) hrel).2.1

end Flapjack
