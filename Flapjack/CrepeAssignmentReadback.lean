import Flapjack.CrepeDeclarationRelation

/-!
Assignment/read-back facts for flattened Crep locals.

Destination-aware calls assign a list of returned words to fresh slots.  The
state relation observes those slots through `readCrepLocals`; this file proves
that the assignment operation has exactly that observable behavior when the
destination list is distinct.
-/

namespace Flapjack

theorem assignCrepValues_read_back
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (resultLocals : Nat → Option α)
    (hassign : assignCrepValues locals names values = some resultLocals)
    (hdistinct : CrepDistinctNames names) :
    readCrepLocals resultLocals names = some values := by
  have hpreserve : ∀ (base : Nat → Option α) (head : Nat) (headValue : α)
      (entries : List (Nat × α)),
      (∀ entry, entry ∈ entries → entry.1 ≠ head) →
      (entries.foldl
          (fun current (name, value) => updateCrepLocal current name value)
          (updateCrepLocal base head headValue)) head = some headValue := by
    intro base head headValue entries
    induction entries generalizing base with
    | nil =>
        intro _
        simp [updateCrepLocal]
    | cons entry entries ih =>
        rcases entry with ⟨entryName, entryValue⟩
        intro hentries
        have hentry : entryName ≠ head := by
          exact hentries (entryName, entryValue) (by simp)
        have htail : ∀ current, current ∈ entries → current.1 ≠ head := by
          intro current hcurrent
          exact hentries current (by simp [hcurrent])
        have hcomm :
            updateCrepLocal (updateCrepLocal base head headValue)
                entryName entryValue =
              updateCrepLocal (updateCrepLocal base entryName entryValue)
                head headValue := by
          funext current
          by_cases hcurrentHead : current = head <;>
            by_cases hcurrentName : current = entryName <;>
            simp [updateCrepLocal, hcurrentHead, hcurrentName, hentry,
              Ne.symm hentry]
        simp only [List.foldl]
        rw [hcomm]
        exact ih (base := updateCrepLocal base entryName entryValue) htail
  have hread : ∀ (base : Nat → Option α) (names : List Nat)
      (values : List α),
      names.length = values.length →
      CrepDistinctNames names →
      readCrepLocals
          ((names.zip values).foldl
            (fun current (name, value) => updateCrepLocal current name value)
            base) names = some values := by
    intro base names
    induction names generalizing base with
    | nil =>
        intro values hlength _
        cases values with
        | nil => simp [readCrepLocals]
        | cons value values => simp at hlength
    | cons head names ih =>
        intro values hlength hdistinct
        cases values with
        | nil => simp at hlength
        | cons headValue values =>
            have hlength' : names.length = values.length := by
              simpa using hlength
            rcases hdistinct with ⟨hnot, htailDistinct⟩
            have hzipFstMem : ∀ (remaining : List Nat)
                (remainingValues : List α) (entry : Nat × α),
                entry ∈ remaining.zip remainingValues → entry.1 ∈ remaining := by
              intro remaining
              induction remaining with
              | nil =>
                  intro remainingValues entry hentry
                  simp at hentry
              | cons current remaining ihRemaining =>
                  intro remainingValues entry
                  cases remainingValues with
                  | nil =>
                      intro hentry
                      simp at hentry
                  | cons currentValue remainingValues =>
                      intro hentry
                      simp only [List.zip_cons_cons, List.mem_cons] at hentry
                      rcases hentry with hentry | hentry
                      · cases hentry
                        simp
                      · exact List.mem_cons_of_mem current
                          (ihRemaining remainingValues entry hentry)
            have hentries : ∀ entry, entry ∈ names.zip values →
                entry.1 ≠ head := by
              intro entry hentry
              have hnameMem : entry.1 ∈ names := by
                exact hzipFstMem names values entry hentry
              intro heq
              apply hnot
              simpa [heq] using hnameMem
            have hhead := hpreserve base head headValue
              (names.zip values) hentries
            have htail := ih
              (base := updateCrepLocal base head headValue)
              values hlength' htailDistinct
            simp only [List.zip_cons_cons, List.foldl, readCrepLocals]
            rw [hhead, htail]
            simp
  have hassign' := hassign
  simp [assignCrepValues] at hassign'
  rcases hassign' with ⟨hlength, hfold⟩
  rw [← hfold]
  exact hread locals names values hlength hdistinct

theorem assignCrepValues_read_preserve
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (resultLocals : Nat → Option α) (slots : List Nat)
    (hassign : assignCrepValues locals names values = some resultLocals)
    (hnot : ∀ name, name ∈ names → name ∉ slots) :
    readCrepLocals resultLocals slots = readCrepLocals locals slots := by
  have hfold : ∀ (base : Nat → Option α) (entries : List (Nat × α)),
      (∀ entry, entry ∈ entries → entry.1 ∉ slots) →
      readCrepLocals
          (entries.foldl
            (fun current (name, value) => updateCrepLocal current name value)
            base) slots = readCrepLocals base slots := by
    intro base entries
    induction entries generalizing base with
    | nil =>
        intro _
        rfl
    | cons entry entries ih =>
        rcases entry with ⟨entryName, entryValue⟩
        intro hentries
        have hentry : entryName ∉ slots := by
          exact hentries (entryName, entryValue) (by simp)
        have htail : ∀ current, current ∈ entries → current.1 ∉ slots := by
          intro current hcurrent
          exact hentries current (by simp [hcurrent])
        simp only [List.foldl]
        rw [ih (base := updateCrepLocal base entryName entryValue) htail]
        exact readCrepLocals_update_of_not_mem base entryName entryValue slots hentry
  have hassign' := hassign
  simp [assignCrepValues] at hassign'
  rcases hassign' with ⟨_, hfoldAssign⟩
  rw [← hfoldAssign]
  have hzipFstMem : ∀ (remaining : List Nat)
      (remainingValues : List α) (entry : Nat × α),
      entry ∈ remaining.zip remainingValues → entry.1 ∈ remaining := by
    intro remaining
    induction remaining with
    | nil =>
        intro remainingValues entry hentry
        simp at hentry
    | cons current remaining ihRemaining =>
        intro remainingValues entry
        cases remainingValues with
        | nil =>
            intro hentry
            simp at hentry
        | cons currentValue remainingValues =>
            intro hentry
            simp only [List.zip_cons_cons, List.mem_cons] at hentry
            rcases hentry with hentry | hentry
            · cases hentry
              simp
            · exact List.mem_cons_of_mem current
                (ihRemaining remainingValues entry hentry)
  apply hfold
  intro entry hentry
  have hnameMem : entry.1 ∈ names := by
    exact hzipFstMem names values entry hentry
  exact hnot entry.1 hnameMem

end Flapjack
