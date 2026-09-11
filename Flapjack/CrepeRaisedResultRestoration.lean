import Flapjack.CrepeDeclarationRelation

/-!
Raised control results do not expose source locals: their Crep relation only
constrains the exception spill and memory.  Consequently compiler-generated
local restoration is semantically irrelevant to a raised result.  These
lemmas make that fact explicit for arbitrary temporary-name lists.
-/

namespace Flapjack

def restoreCrepLocalList {α : Type u} [OfNat α 0]
    (locals : Nat → Option α) : List Nat →
    (Nat → Option α) → Nat → Option α
  | [], resultLocals => resultLocals
  | name :: names, resultLocals =>
      restoreCrepLocal
        (restoreCrepLocalList (updateCrepLocal locals name 0) names resultLocals)
        name (locals name)

theorem restoreCrepResultList_raised
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat)
    (state : CrepState α) (exception : α) :
    restoreCrepResultList locals names (.raised state exception) =
      .raised
        { state with
            locals := restoreCrepLocalList locals names state.locals }
        exception := by
  induction names generalizing locals state with
  | nil =>
      simp [restoreCrepResultList, restoreCrepLocalList]
  | cons name names ih =>
      simp only [restoreCrepResultList]
      rw [ih (locals := updateCrepLocal locals name 0)]
      rfl

theorem panValueCrepControlRel_restore_local_raised
    [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (state : CrepState α) (exceptionCode : α)
    (newLocals : Nat → Option α)
    (hrel : panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised state exceptionCode)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised { state with locals := newLocals } exceptionCode) := by
  obtain ⟨spillAddress, hstate, hexception⟩ := hrel
  refine ⟨spillAddress, ?_, hexception⟩
  exact ⟨hstate.1, panValueCrepLocalsRel_empty structs context newLocals,
    hstate.2.2⟩

theorem panValueCrepControlRel_restore_raised_list
    [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (state : CrepState α) (exceptionCode : α)
    (names : List Nat)
    (hrel : panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised state exceptionCode)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (restoreCrepResultList state.locals names
        (.raised state exceptionCode)) := by
  rw [restoreCrepResultList_raised]
  exact panValueCrepControlRel_restore_local_raised structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    state exceptionCode (restoreCrepLocalList state.locals names state.locals) hrel

end Flapjack
