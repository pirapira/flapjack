import Flapjack.CrepeRecordDeclarationRestorationRelation

/-!
Transport the complete source/Crep control relation through a two-word
declaration boundary.  This packages the state-restoration argument for all
terminal outcomes so the general declaration correctness case can focus on
evaluating the declaration value and its body.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepControlRel_restore_two_word_declaration
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (context : CompileContext α)
    (oldValue : Option (PanValue α)) (state : CrepState α)
    (name : VarName)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots ∧ context.maxVar + 2 ∉ oldSlots)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hrel : panValueCrepControlRel structs
      { context with
          vars := (name, (.comb [.one, .one],
            [context.maxVar + 1, context.maxVar + 2])) :: context.vars
          maxVar := context.maxVar + 2 }
      exceptionRel sourceResult crepResult) :
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name oldValue sourceResult)
      (restoreCrepResultList state.locals
        [context.maxVar + 1, context.maxVar + 2] crepResult) := by
  cases sourceResult with
  | normal bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState =>
          have hstate := panValueCrepStateRel_restore_two_word_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList, restoreCrepResult, updateCrepLocal,
            Nat.add_assoc] using hstate
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | returned bodyLocals bodyGlobals bodyMemory values =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState crepValues =>
          have hstate := panValueCrepStateRel_restore_two_word_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name hname hfresh hrel.1
          have hvalues : panValueCrepValuesRel values crepValues := hrel.2
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList, restoreCrepResult, updateCrepLocal,
            Nat.add_assoc] using And.intro hstate hvalues
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | raised bodyLocals bodyGlobals bodyMemory exception value =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exceptionCode =>
          obtain ⟨spillAddress, hstate, hexception⟩ := hrel
          have hrestoredState :
              panValueCrepRaisedStateRel structs context bodyGlobals bodyMemory
                { bodyState with locals :=
                    (restoreCrepLocal
                      (restoreCrepLocal bodyState.locals
                        (context.maxVar + 2) (state.locals (context.maxVar + 2)))
                      (context.maxVar + 1) (state.locals (context.maxVar + 1))) }
                spillAddress := by
            refine ⟨hstate.1, ?_, hstate.2.2⟩
            intro current currentValue shape slots hcurrent hlookup
            simp at hcurrent
          have hresult :
              panValueCrepRaisedControlRel structs context exceptionRel
                bodyGlobals bodyMemory exception value
                { bodyState with locals :=
                    (restoreCrepLocal
                      (restoreCrepLocal bodyState.locals
                        (context.maxVar + 2) (state.locals (context.maxVar + 2)))
                      (context.maxVar + 1) (state.locals (context.maxVar + 1))) }
                exceptionCode spillAddress :=
            ⟨hrestoredState, hexception⟩
          have hresult' : ∃ spillAddress,
              panValueCrepRaisedControlRel structs context exceptionRel
                bodyGlobals bodyMemory exception value
                { bodyState with locals :=
                    (restoreCrepLocal
                      (restoreCrepLocal bodyState.locals
                        (context.maxVar + 2) (state.locals (context.maxVar + 2)))
                      (context.maxVar + 1) (state.locals (context.maxVar + 1))) }
                exceptionCode spillAddress :=
            ⟨spillAddress, hresult⟩
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList, restoreCrepResult, updateCrepLocal,
            Nat.add_assoc] using hresult'
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | broke bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label =>
          have hstate := panValueCrepStateRel_restore_two_word_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList, restoreCrepResult, updateCrepLocal,
            Nat.add_assoc] using hstate
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | continued bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label =>
          have hstate := panValueCrepStateRel_restore_two_word_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList, restoreCrepResult, updateCrepLocal,
            Nat.add_assoc] using hstate
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel

end Flapjack
