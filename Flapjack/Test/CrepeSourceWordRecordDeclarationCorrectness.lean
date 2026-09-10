import Flapjack.CrepeSourceWordRecordDeclarationCorrectness

namespace Flapjack

def sourceWordRecordDeclarationContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordRecordDeclarationState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_record_declaration_relation :
    panValueCrepStateRel []
      { sourceWordRecordDeclarationContext with
          vars := [("x", (.comb [.one, .one], [1, 2]))]
          maxVar := 2 }
      (updatePanValueMap (fun _ => none) "x"
        (.rStruct [.word 3, .word 4])) (fun _ => none) (fun _ => none)
      { sourceWordRecordDeclarationState with locals :=
          (updateCrepLocal
            (updateCrepLocal sourceWordRecordDeclarationState.locals 1 3)
            2 4) } := by
  have hrel : panValueCrepStateRel [] sourceWordRecordDeclarationContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordRecordDeclarationState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty []
      sourceWordRecordDeclarationContext _, rfl⟩
  exact panValueCrepStateRel_extend_record_two_words
    [] sourceWordRecordDeclarationContext (fun _ => none) (fun _ => none)
    (fun _ => none) sourceWordRecordDeclarationState "x" 3 4 hrel
    (by simp [panValueShape, panShapeMatches,
      panShapeMatches.panShapeListMatches])
    (by simp [readCrepLocals, updateCrepLocal])
    (by
      intro oldName oldValue oldShape oldSlots hne hsource hlookup
      simp [sourceWordRecordDeclarationContext, lookupInfo] at hlookup)
    (by
      intro oldName oldShape oldSlots hne hlookup
      simp [sourceWordRecordDeclarationContext, lookupInfo] at hlookup)

end Flapjack
