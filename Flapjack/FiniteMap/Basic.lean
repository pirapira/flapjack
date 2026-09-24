import Flapjack.HolRef

/-!
Primitive HOL4/CakeML finite-map interface.

CakeML's `('a,'b) fmap` (`finite_mapTheory`) is a total function with finite
support; `FLOOKUP`, `FUPDATE` (`|+`), `FUPDATE_LIST` (`|++`) and `FEMPTY` are
its observable interface.  We represent it here as `α → Option β`, which is
extensionally the same object and makes the HOL equations definitional.

This module holds only the primitive interface and its immediate equations, so
that lower-level compiler modules (for example `Flapjack.Pancake.PanToCrep`,
whose HOL source uses `FLOOKUP`) can cite it without depending on the
proof-layer module `Flapjack.FiniteMap`, which imports the Pan-to-Crep compiler.
-/

namespace Flapjack

/-- CakeML/HOL `('a,'b) fmap`, represented as a total function. -/
abbrev FiniteMap (α β : Type) := α → Option β

/-- Cake `FLOOKUP` (`finite_mapTheory.FLOOKUP_DEF`). -/
def FLOOKUP (f : FiniteMap α β) (key : α) : Option β := f key

/-- Cake `FEMPTY`. -/
def FEMPTY : FiniteMap α β := fun _ => none

/-- Cake `FUPDATE` (`|+`, `finite_mapTheory.FUPDATE_DEF`). -/
def FUPDATE [BEq α] (f : FiniteMap α β) (entry : α × β) : FiniteMap α β :=
  fun key => if entry.1 == key then some entry.2 else f key

/-- Cake `FUPDATE_LIST` (`|++`, `finite_mapTheory.FUPDATE_LIST`), i.e.
`FOLDL FUPDATE`. -/
def FUPDATE_LIST [BEq α] (f : FiniteMap α β) (entries : List (α × β)) : FiniteMap α β :=
  entries.foldl (fun g entry => FUPDATE g entry) f

/-- Cake `FDOM`: the keys whose lookup is defined. -/
def FDOM (f : FiniteMap α β) : α → Prop := fun key => f key ≠ none

@[simp] theorem FLOOKUP_empty (key : α) :
    FLOOKUP (FEMPTY : FiniteMap α β) key = none := rfl

/-- Cake `FLOOKUP_UPDATE` (`finite_mapTheory.FLOOKUP_UPDATE`). -/
theorem FLOOKUP_update [BEq α] [LawfulBEq α] (f : FiniteMap α β)
    (k1 : α) (v : β) (k2 : α) :
    FLOOKUP (FUPDATE f (k1, v)) k2 = if k1 == k2 then some v else FLOOKUP f k2 :=
  rfl

/-- Cake `FUPDATE_LIST_THM`, nil case. -/
theorem FUPDATE_LIST_nil [BEq α] (f : FiniteMap α β) :
    FUPDATE_LIST f [] = f := rfl

/-- Cake `FUPDATE_LIST_THM`, cons case. -/
theorem FUPDATE_LIST_cons [BEq α] (f : FiniteMap α β) (entry : α × β)
    (entries : List (α × β)) :
    FUPDATE_LIST f (entry :: entries) = FUPDATE_LIST (FUPDATE f entry) entries := rfl

/-- Cake `FUPDATE_LIST_APPLY_NOT_MEM`: updating keys other than `k` does not
change the lookup at `k`. -/
theorem FLOOKUP_FUPDATE_LIST_not_mem [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (entries : List (α × β)) (k : α)
    (h : k ∉ entries.map Prod.fst) :
    FLOOKUP (FUPDATE_LIST f entries) k = FLOOKUP f k := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
    have hk : entry.1 ≠ k := by
      intro he
      exact h (by simp [he])
    have htail : k ∉ entries.map Prod.fst := by
      intro hmem
      exact h (by simp [hmem])
    rw [FUPDATE_LIST_cons, ih (FUPDATE f entry) htail, FLOOKUP_update]
    have hbf : (entry.1 == k) = false := beq_eq_false_iff_ne.mpr hk
    simp [hbf]

/-! Inverse support fact for finite-map reasoning: a successful lookup after a
list of updates either came from one of those entries or from the base map.
This is Flapjack-specific finite-map infrastructure; it is not a standalone
HOL theorem port. -/
theorem flookupFupdateList_mem_or_base [BEq α] [LawfulBEq α]
    (base : FiniteMap α β) (entries : List (α × β)) (key : α) (value : β)
    (hlookup : FLOOKUP (FUPDATE_LIST base entries) key = some value) :
    (∃ entry, entry ∈ entries ∧ entry.1 = key ∧ entry.2 = value) ∨
      FLOOKUP base key = some value := by
  induction entries generalizing base with
  | nil =>
      simp only [FUPDATE_LIST_nil] at hlookup
      exact Or.inr hlookup
  | cons entry entries ih =>
      rcases entry with ⟨entryKey, entryValue⟩
      rw [FUPDATE_LIST_cons] at hlookup
      rcases ih (FUPDATE base (entryKey, entryValue)) hlookup with htail | hbase
      · rcases htail with ⟨tailEntry, hmem, hkey, hvalue⟩
        exact Or.inl ⟨tailEntry, by simp [hmem], hkey, hvalue⟩
      · by_cases heq : entryKey == key
        · have hvalueEq : entryValue = value := by
            simpa [FLOOKUP_update, heq] using hbase
          exact Or.inl ⟨(entryKey, entryValue), by simp,
            beq_iff_eq.mp heq, hvalueEq⟩
        · have hbaseLookup : FLOOKUP base key = some value := by
            simpa [FLOOKUP_update, heq] using hbase
          exact Or.inr hbaseLookup

/-- Two single updates at distinct keys commute. -/
theorem FUPDATE_comm [BEq α] [LawfulBEq α] (f : FiniteMap α β)
    (k1 : α) (v1 : β) (k2 : α) (v2 : β) (h : k1 ≠ k2) :
    FUPDATE (FUPDATE f (k1, v1)) (k2, v2) =
      FUPDATE (FUPDATE f (k2, v2)) (k1, v1) := by
  funext key
  unfold FUPDATE
  by_cases h2 : k2 == key
  · have hk2 : k2 = key := beq_iff_eq.mp h2
    have h1 : (k1 == key) = false := by
      have hne : k1 ≠ key := fun he => h (he.trans hk2.symm)
      exact beq_eq_false_iff_ne.mpr hne
    simp [h2, h1]
  · have hk2 : key ≠ k2 := fun he => h2 (beq_iff_eq.mpr he.symm)
    have h2f : (k2 == key) = false := beq_eq_false_iff_ne.mpr (fun he => hk2 he.symm)
    by_cases h1 : k1 == key <;> simp [h2f, h1]

/-- Flapjack-specific analogue of Cake `FUPDATE_FUPDATE_LIST_COMMUTES` (not an
exact HOL port, since it is proved over this file's extensional representation):
a single update at a key absent from the update list commutes with the whole
list update. -/
theorem FUPDATE_FUPDATE_LIST_commutes [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (k : α) (v : β) (entries : List (α × β))
    (h : k ∉ entries.map Prod.fst) :
    FUPDATE (FUPDATE_LIST f entries) (k, v) =
      FUPDATE_LIST (FUPDATE f (k, v)) entries := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
    have hk : entry.1 ≠ k := by
      intro he
      exact h (by simp [he])
    have htail : k ∉ entries.map Prod.fst := by
      intro hmem
      exact h (by simp [hmem])
    rw [FUPDATE_LIST_cons (f := FUPDATE f (k, v)) (entry := entry) (entries := entries)]
    rw [FUPDATE_LIST_cons (f := f) (entry := entry) (entries := entries)]
    rw [ih (FUPDATE f entry) htail]
    rw [FUPDATE_comm f entry.1 entry.2 k v hk]


/-- Flapjack representation of HOL4's `\\` (domain subtraction) on finite
maps: `FDOMSUB f key` removes `key` from the domain of `f`. -/
def FDOMSUB [BEq α] (f : FiniteMap α β) (key : α) : FiniteMap α β :=
  fun k => if key == k then none else f k

/-- Exact port of Cake's `res_var_def`
(cakeml/pancake/semantics/crepSemScript.sml:163): `res_var lc (n, NONE) = lc \\ n`
and `res_var lc (n, SOME v) = lc |+ (n,v)`, with `\\` rendered as `FDOMSUB` and
`|+` as `FUPDATE`.  `[LawfulBEq α]` ties the Boolean equality to HOL's
propositional equality. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "res_var_def"]
def resVar [BEq α] [LawfulBEq α] (f : FiniteMap α β) (entry : α × Option β) : FiniteMap α β :=
  match entry.2 with
  | none => FDOMSUB f entry.1
  | some v => FUPDATE f (entry.1, v)

end Flapjack
