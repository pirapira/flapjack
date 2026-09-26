
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


/-- Cake's `DISJOINT (set left) (set right)` predicate, stated directly on
    lists because `List` membership already expresses the element relation. -/
def ListDisjoint (left right : List α) : Prop :=
  ∀ value, value ∈ left → value ∈ right → False

theorem FLOOKUP_domsub [BEq α] [LawfulBEq α] (f : FiniteMap α β) (key k : α) :
    FLOOKUP (FDOMSUB f key) k = if key == k then none else FLOOKUP f k := rfl

theorem FDOMSUB_FUPDATE_neq [BEq α] [LawfulBEq α] (f : FiniteMap α β) (key m : α) (v : β)
    (h : key ≠ m) :
    FDOMSUB (FUPDATE f (m, v)) key = FUPDATE (FDOMSUB f key) (m, v) := by
  funext k
  simp only [FDOMSUB, FUPDATE]
  by_cases hkm : m == k
  · simp only [hkm, if_true]
    have hkm' : k = m := (beq_iff_eq.mp hkm).symm
    have hkeyk : (key == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      exact h (hc.trans hkm')
    simp only [hkeyk, Bool.false_eq_true, if_false]
  · simp only [hkm, Bool.false_eq_true, if_false]

theorem FDOMSUB_commutes [BEq α] [LawfulBEq α] (f : FiniteMap α β) (n m : α)
    (h : n ≠ m) : FDOMSUB (FDOMSUB f n) m = FDOMSUB (FDOMSUB f m) n := by
  funext k
  simp only [FDOMSUB]
  by_cases hmn : m == k
  · have hmn' : k = m := (beq_iff_eq.mp hmn).symm
    have hnk : (n == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      exact h (hc.trans hmn')
    simp only [hmn, if_true, hnk, Bool.false_eq_true, if_false]
  · by_cases hnk : n == k
    · have hnk' : k = n := (beq_iff_eq.mp hnk).symm
      have hmk : (m == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (hnk'.symm.trans hc.symm)
      simp only [hnk, if_true, hmk, Bool.false_eq_true, if_false]
    · simp only [hmn, hnk, Bool.false_eq_true, if_false]

theorem FLOOKUP_FUPDATE_LIST_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (f : FiniteMap α β) (n : α)
    (hlen : xs.length = ys.length) (h : n ∉ xs) :
    FLOOKUP (FUPDATE_LIST f (xs.zip ys)) n = FLOOKUP f n := by
  apply FLOOKUP_FUPDATE_LIST_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

theorem map_FLOOKUP_FUPDATE_LIST_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (zs : List β) (f : FiniteMap α β)
    (hdisj : ListDisjoint xs ys) (hlen : xs.length = zs.length) :
    ys.map (fun y => FLOOKUP (FUPDATE_LIST f (xs.zip zs)) y) =
      ys.map (fun y => FLOOKUP f y) := by
  revert hdisj
  induction ys with
  | nil => intro _; rfl
  | cons y rest ih =>
    intro hdisj
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · exact FLOOKUP_FUPDATE_LIST_zip_not_mem xs zs f y hlen
        (fun hy => hdisj y hy (by simp))
    · exact ih (fun v hv hmem => hdisj v hv (by simp [hmem]))

/-- Flapjack-specific analogue of Cake `domsub_commutes_fupdate`
(pan_commonPropsScript.sml:319); not an exact HOL port, since it is stated over
the Boolean-`BEq` `FDOMSUB`: domain subtraction at a key absent from the update
list commutes with the list update. -/
theorem FDOMSUB_FUPDATE_LIST_commutes [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (fm : FiniteMap α β) (x : α)
    (h : x ∉ xs) (hlen : xs.length = ys.length) :
    FDOMSUB (FUPDATE_LIST fm (xs.zip ys)) x =
      FUPDATE_LIST (FDOMSUB fm x) (xs.zip ys) := by
  induction xs generalizing fm ys with
  | nil =>
    cases ys with
    | nil => simp [FUPDATE_LIST_nil]
    | cons y ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hne : x ≠ a := by
        intro he
        exact h (by simp [he])
      have htail : x ∉ xs := by
        intro hmem
        exact h (by simp [hmem])
      have hlenTail : xs.length = ys.length := by simpa using hlen
      rw [List.zip_cons_cons, FUPDATE_LIST_cons]
      rw [ih ys (FUPDATE fm (a, y)) htail hlenTail]
      rw [FDOMSUB_FUPDATE_neq fm x a y hne]
      rw [FUPDATE_LIST_cons]

/-- Flapjack-specific analogue of Cake `update_eq_zip_flookup`
(pan_commonPropsScript.sml:244); not an exact HOL port: a key occurring in a
distinct key list looks up its paired value in the updated map. -/
theorem FLOOKUP_FUPDATE_LIST_zip_getElem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (f : FiniteMap α β) (n : Nat)
    (hdistinct : xs.Nodup) (hlen : xs.length = ys.length) (hn : n < xs.length) :
    FLOOKUP (FUPDATE_LIST f (xs.zip ys)) (xs[n]'hn) =
      some (ys[n]'(by rw [← hlen]; exact hn)) := by
  induction xs generalizing f ys n with
  | nil => simp at hn
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.nodup_cons] at hdistinct
      obtain ⟨ha, hdistinctTail⟩ := hdistinct
      have hlenTail : xs.length = ys.length := by simpa using hlen
      cases n with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [List.zip_cons_cons, FUPDATE_LIST_cons]
        rw [FLOOKUP_FUPDATE_LIST_not_mem (FUPDATE f (a, y)) (xs.zip ys) a
          (by rw [List.map_fst_zip (by omega)]; exact ha)]
        rw [FLOOKUP_update]
        simp
      | succ k =>
        have hk : k < xs.length := by
          simp only [List.length_cons] at hn
          omega
        simp only [List.getElem_cons_succ]
        rw [List.zip_cons_cons, FUPDATE_LIST_cons]
        exact ih ys (FUPDATE f (a, y)) k hdistinctTail hlenTail hk

/-- Domain subtraction at a key that is not bound leaves the map unchanged. -/
theorem FDOMSUB_eq_self_of_lookup_none [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (h : FLOOKUP f x = none) :
    FDOMSUB f x = f := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FDOMSUB, hk, if_true]
    rw [← beq_iff_eq.mp hk]
    exact h.symm
  · simp only [FDOMSUB, hk, Bool.false_eq_true, if_false]

/-- Updating a key with the value it already binds leaves the map unchanged. -/
theorem FUPDATE_eq_self_of_lookup_some [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v : β) (h : FLOOKUP f x = some v) :
    FUPDATE f (x, v) = f := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FUPDATE, hk, if_true]
    rw [← beq_iff_eq.mp hk]
    exact h.symm
  · simp only [FUPDATE, hk, Bool.false_eq_true, if_false]

/-- Domain subtraction at a key immediately after updating that same key. -/
theorem FDOMSUB_FUPDATE_same [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v : β) :
    FDOMSUB (FUPDATE f (x, v)) x = FDOMSUB f x := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FDOMSUB, FUPDATE, hk, if_true]
  · simp only [FDOMSUB, FUPDATE, hk, Bool.false_eq_true, if_false]

/-- Two consecutive updates of the same key collapse to the later one. -/
theorem FUPDATE_FUPDATE_same [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v1 v2 : β) :
    FUPDATE (FUPDATE f (x, v1)) (x, v2) = FUPDATE f (x, v2) := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FUPDATE, hk, if_true]
  · simp only [FUPDATE, hk, Bool.false_eq_true, if_false]

/-! ## HOL-equality (`=`) finite-map primitives

HOL's `finite_mapTheory` defines `FUPDATE` (`|+`), `FUPDATE_LIST` (`|++`) and
domain subtraction (`\\`) with the polymorphic propositional equality `=`.  The
primitives above use the Boolean `BEq` because that is what the executable
compiler runs.  The definitions below are the faithful `=`-based representation
(`DecidableEq` is Lean's direct encoding of HOL equality, which is decidable at
every type), so HOL statements that quantify the key type freely can be ported
statement-exactly.  These are Flapjack infrastructure, not declarations of a
CakeML script. -/

/-- HOL-equality form of `FUPDATE` (`|+`). -/
def FUPDATE_HOL [DecidableEq α] (f : FiniteMap α β) (entry : α × β) : FiniteMap α β :=
  fun key => if key = entry.1 then some entry.2 else f key

/-- HOL-equality form of `FUPDATE_LIST` (`|++`), i.e. `FOLDL FUPDATE`. -/
def FUPDATE_LIST_HOL [DecidableEq α] (f : FiniteMap α β)
    (entries : List (α × β)) : FiniteMap α β :=
  entries.foldl (fun g entry => FUPDATE_HOL g entry) f

/-- HOL-equality form of domain subtraction (`\\`). -/
def FDOMSUB_HOL [DecidableEq α] (f : FiniteMap α β) (key : α) : FiniteMap α β :=
  fun k => if k = key then none else f k

@[simp] theorem FLOOKUP_FUPDATE_HOL [DecidableEq α] (f : FiniteMap α β)
    (k1 : α) (v : β) (k2 : α) :
    FLOOKUP (FUPDATE_HOL f (k1, v)) k2 = if k2 = k1 then some v else FLOOKUP f k2 :=
  rfl

@[simp] theorem FLOOKUP_FDOMSUB_HOL [DecidableEq α] (f : FiniteMap α β) (key k : α) :
    FLOOKUP (FDOMSUB_HOL f key) k = if k = key then none else FLOOKUP f k :=
  rfl

@[simp] theorem FUPDATE_LIST_HOL_nil [DecidableEq α] (f : FiniteMap α β) :
    FUPDATE_LIST_HOL f [] = f := rfl

theorem FUPDATE_LIST_HOL_cons [DecidableEq α] (f : FiniteMap α β) (entry : α × β)
    (entries : List (α × β)) :
    FUPDATE_LIST_HOL f (entry :: entries) =
      FUPDATE_LIST_HOL (FUPDATE_HOL f entry) entries :=
  rfl

/-- For a lawful `BEq`, the HOL-equality `FUPDATE_HOL` agrees with the Boolean
    `FUPDATE`; this lets equality-based state helpers reuse the executable
    bridges proved for the `BEq`-based maps. -/
theorem FUPDATE_HOL_eq_FUPDATE [DecidableEq α] [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (entry : α × β) :
    FUPDATE_HOL f entry = FUPDATE f entry := by
  funext k
  unfold FUPDATE_HOL FUPDATE
  by_cases h : k = entry.1
  · rw [if_pos h, if_pos (beq_iff_eq.mpr h.symm)]
  · rw [if_neg h, if_neg (fun hb => h (beq_iff_eq.mp hb).symm)]

/-- List-level agreement of the equality-based and Boolean `FUPDATE_LIST`. -/
theorem FUPDATE_LIST_HOL_eq_FUPDATE_LIST [DecidableEq α] [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (entries : List (α × β)) :
    FUPDATE_LIST_HOL f entries = FUPDATE_LIST f entries := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry rest ih =>
      rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_cons, FUPDATE_HOL_eq_FUPDATE, ih]

/-- HOL-equality form of `FUPDATE` commutation at distinct keys. -/
theorem FUPDATE_HOL_comm [DecidableEq α] (f : FiniteMap α β)
    (k1 : α) (v1 : β) (k2 : α) (v2 : β) (h : k1 ≠ k2) :
    FUPDATE_HOL (FUPDATE_HOL f (k1, v1)) (k2, v2) =
      FUPDATE_HOL (FUPDATE_HOL f (k2, v2)) (k1, v1) := by
  funext key
  by_cases h2 : key = k2 <;> by_cases h1 : key = k1 <;>
    simp_all [FUPDATE_HOL]

/-- HOL-equality form of domain subtraction commutes at distinct keys. -/
theorem FDOMSUB_HOL_commutes [DecidableEq α] (f : FiniteMap α β) (n m : α)
    (h : n ≠ m) : FDOMSUB_HOL (FDOMSUB_HOL f n) m = FDOMSUB_HOL (FDOMSUB_HOL f m) n := by
  funext k
  by_cases hk : k = m <;> by_cases hk' : k = n <;>
    simp_all [FDOMSUB_HOL]

/-- HOL-equality form of `\\` after `|+` at a distinct key. -/
theorem FDOMSUB_HOL_FUPDATE_HOL_neq [DecidableEq α] (f : FiniteMap α β)
    (key m : α) (v : β) (h : key ≠ m) :
    FDOMSUB_HOL (FUPDATE_HOL f (m, v)) key =
      FUPDATE_HOL (FDOMSUB_HOL f key) (m, v) := by
  funext k
  by_cases hk : k = m <;> by_cases hk2 : k = key <;>
    simp_all [FDOMSUB_HOL, FUPDATE_HOL]

/-- HOL-equality form of `FLOOKUP_FUPDATE_LIST_NOT_MEM`. -/
theorem FLOOKUP_FUPDATE_LIST_HOL_not_mem [DecidableEq α] (f : FiniteMap α β)
    (entries : List (α × β)) (k : α) (h : k ∉ entries.map Prod.fst) :
    FLOOKUP (FUPDATE_LIST_HOL f entries) k = FLOOKUP f k := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
    have hk : entry.1 ≠ k := fun he => h (by simp [he])
    have htail : k ∉ entries.map Prod.fst := fun hmem => h (by simp [hmem])
    rw [FUPDATE_LIST_HOL_cons, ih (FUPDATE_HOL f entry) htail]
    simp only [FLOOKUP, FUPDATE_HOL]
    have hk' : ¬ k = entry.1 := fun hc => hk hc.symm
    simp [hk']

end Flapjack
