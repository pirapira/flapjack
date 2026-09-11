import Flapjack.CrepeDeclarationRestorationRelation

/-!
Lift arbitrary-shape declaration restoration through the source/Crep control
relation.  Raised results use the dedicated raised-restoration lemma because
their local relation is intentionally empty.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepControlRel_restore_declaration
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (context : CompileContext α)
    (oldValue : Option (PanValue α)) (state : CrepState α)
    (name : VarName) (shape : Shape) (names : List Nat)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ names → temporary ∉ oldSlots)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hrel : panValueCrepControlRel structs
      { context with
          vars := (name, (shape, names)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      exceptionRel sourceResult crepResult) :
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name oldValue sourceResult)
      (restoreCrepResultList state.locals names crepResult) := by
  cases sourceResult with
  | normal bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState =>
          have hstate := panValueCrepStateRel_restore_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name shape names hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList_normal] using hstate
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | returned bodyLocals bodyGlobals bodyMemory values =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState crepValues =>
          have hstate := panValueCrepStateRel_restore_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name shape names hname hfresh hrel.1
          have hvalues : panValueCrepValuesRel values crepValues := hrel.2
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList_returned] using And.intro hstate hvalues
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | raised bodyLocals bodyGlobals bodyMemory exception value =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exceptionCode =>
          have houterRel :
              panValueCrepControlRel structs context exceptionRel
                (.raised bodyLocals bodyGlobals bodyMemory exception value)
                (.raised bodyState exceptionCode) := by
            obtain ⟨spillAddress, hstate, hexception⟩ := hrel
            refine ⟨spillAddress, ?_, hexception⟩
            exact ⟨hstate.1,
              panValueCrepLocalsRel_empty structs context bodyState.locals,
              hstate.2.2⟩
          have hresult : ∃ spillAddress,
              panValueCrepRaisedControlRel structs context exceptionRel
                bodyGlobals bodyMemory exception value
                { bodyState with locals :=
                    restoreCrepLocalList state.locals names bodyState.locals }
                exceptionCode spillAddress := by
            exact panValueCrepControlRel_restore_local_raised
              structs context exceptionRel bodyLocals bodyGlobals bodyMemory
              exception value bodyState exceptionCode
              (restoreCrepLocalList state.locals names bodyState.locals)
              houterRel
          simpa only [restorePanValueControlLocal, restoreCrepResultList_raised,
            panValueCrepControlRel] using hresult
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | broke bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label =>
          have hstate := panValueCrepStateRel_restore_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name shape names hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList_broke] using hstate
      | continued bodyState label => simp [panValueCrepControlRel] at hrel
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel
  | continued bodyLocals bodyGlobals bodyMemory =>
      cases crepResult with
      | normal bodyState => simp [panValueCrepControlRel] at hrel
      | returned bodyState values => simp [panValueCrepControlRel] at hrel
      | raised bodyState exception => simp [panValueCrepControlRel] at hrel
      | broke bodyState label => simp [panValueCrepControlRel] at hrel
      | continued bodyState label =>
          have hstate := panValueCrepStateRel_restore_declaration
            structs context oldValue bodyLocals bodyGlobals bodyMemory
            state bodyState name shape names hname hfresh hrel
          simpa [panValueCrepControlRel, restorePanValueControlLocal,
            restoreCrepResultList_continued] using hstate
      | finalFfi bodyState event => simp [panValueCrepControlRel] at hrel

end Flapjack
