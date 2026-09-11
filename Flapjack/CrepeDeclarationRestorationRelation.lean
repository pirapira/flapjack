import Flapjack.CrepeRaisedResultRestoration

/-!
Shape-independent restoration of compiler-generated declaration temporaries.

The allocated names are passed explicitly because the same relation is useful
for declarations and declaration calls.  The only freshness obligation is
that an outer binding's slots do not overlap the temporary list.
-/

namespace Flapjack

theorem panValueCrepStateRel_restore_declaration
    [BEq α] [LawfulBEq α] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (oldValue : Option (PanValue α))
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α))
    (state bodyState : CrepState α) (name : VarName)
    (shape : Shape) (names : List Nat)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ names → temporary ∉ oldSlots)
    (hrel : panValueCrepStateRel structs
      { context with
          vars := (name, (shape, names)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      bodyLocals bodyGlobals bodyMemory bodyState) :
    panValueCrepStateRel structs context
      (restorePanValueLocal bodyLocals name oldValue)
      bodyGlobals bodyMemory
      { bodyState with locals :=
          restoreCrepLocalList state.locals names bodyState.locals } := by
  have hreadRestore : ∀ (locals : Nat → Option α) (temporaryNames : List Nat)
      (resultLocals : Nat → Option α) (slots : List Nat),
      (∀ temporary, temporary ∈ temporaryNames → temporary ∉ slots) →
      readCrepLocals
          (restoreCrepLocalList locals temporaryNames resultLocals) slots =
        readCrepLocals resultLocals slots := by
    have hrestoreRead : ∀ (locals : Nat → Option α) (temporary : Nat)
        (oldValue : Option α) (slots : List Nat),
        temporary ∉ slots →
        readCrepLocals (restoreCrepLocal locals temporary oldValue) slots =
          readCrepLocals locals slots := by
      intro locals temporary oldValue slots
      induction slots with
      | nil =>
          intro _
          rfl
      | cons head tail ih =>
          intro hnot
          have hhead : head ≠ temporary := by
            intro heq
            apply hnot
            simp [heq]
          have htail : temporary ∉ tail := by
            intro hmem
            apply hnot
            simp [hmem]
          simp [readCrepLocals, restoreCrepLocal, hhead, ih htail]
    intro locals temporaryNames
    induction temporaryNames generalizing locals with
    | nil =>
        intro resultLocals slots _
        rfl
    | cons temporary temporaryNames ih =>
        intro resultLocals slots hnot
        have htemporary : temporary ∉ slots := by
          exact hnot temporary (by simp)
        have htail : ∀ current, current ∈ temporaryNames → current ∉ slots := by
          intro current hcurrent
          exact hnot current (by simp [hcurrent])
        change readCrepLocals
            (restoreCrepLocal
              (restoreCrepLocalList (updateCrepLocal locals temporary 0)
                temporaryNames resultLocals)
              temporary (locals temporary)) slots =
          readCrepLocals resultLocals slots
        rw [hrestoreRead _ _ _ _ htemporary]
        exact ih (locals := updateCrepLocal locals temporary 0)
          resultLocals slots htail
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro current currentValue currentShape currentSlots hcurrent hlookup
  by_cases hcurrentName : current == name
  · have heq : current = name := by simpa using hcurrentName
    subst current
    rw [hname] at hlookup
    cases hlookup
  · have hbodyCurrent : bodyLocals current = some currentValue := by
      simp [restorePanValueLocal, hcurrentName] at hcurrent
      exact hcurrent
    have hnameCurrent : name ≠ current := by
      intro heq
      apply hcurrentName
      simp [heq]
    have hlookupBody :
        lookupInfo current ((name, (shape, names)) :: context.vars) =
          some (currentShape, currentSlots) := by
      simp [lookupInfo, hnameCurrent, hlookup]
    have hbodyRel := hrel.2.1 current currentValue currentShape currentSlots
      hbodyCurrent hlookupBody
    have hnot := hfresh current currentShape currentSlots
      (by simpa using hcurrentName) hlookup
    exact ⟨hbodyRel.1,
      (hreadRestore state.locals names bodyState.locals currentSlots hnot).symm
        ▸ hbodyRel.2⟩

theorem restoreCrepResultList_normal
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat)
    (state : CrepState α) :
    restoreCrepResultList locals names (.normal state) =
      .normal
        { state with
            locals := restoreCrepLocalList locals names state.locals } := by
  induction names generalizing locals state with
  | nil =>
      simp [restoreCrepResultList, restoreCrepLocalList]
  | cons name names ih =>
      simp only [restoreCrepResultList]
      rw [ih (locals := updateCrepLocal locals name 0)]
      rfl

theorem restoreCrepResultList_returned
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat)
    (state : CrepState α) (values : List α) :
    restoreCrepResultList locals names (.returned state values) =
      .returned
        { state with
            locals := restoreCrepLocalList locals names state.locals }
        values := by
  induction names generalizing locals state with
  | nil =>
      simp [restoreCrepResultList, restoreCrepLocalList]
  | cons name names ih =>
      simp only [restoreCrepResultList]
      rw [ih (locals := updateCrepLocal locals name 0)]
      rfl

theorem restoreCrepResultList_broke
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat)
    (state : CrepState α) (label : Nat) :
    restoreCrepResultList locals names (.broke state label) =
      .broke
        { state with
            locals := restoreCrepLocalList locals names state.locals }
        label := by
  induction names generalizing locals state with
  | nil =>
      simp [restoreCrepResultList, restoreCrepLocalList]
  | cons name names ih =>
      simp only [restoreCrepResultList]
      rw [ih (locals := updateCrepLocal locals name 0)]
      rfl

theorem restoreCrepResultList_continued
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat)
    (state : CrepState α) (label : Nat) :
    restoreCrepResultList locals names (.continued state label) =
      .continued
        { state with
            locals := restoreCrepLocalList locals names state.locals }
        label := by
  induction names generalizing locals state with
  | nil =>
      simp [restoreCrepResultList, restoreCrepLocalList]
  | cons name names ih =>
      simp only [restoreCrepResultList]
      rw [ih (locals := updateCrepLocal locals name 0)]
      rfl

end Flapjack
