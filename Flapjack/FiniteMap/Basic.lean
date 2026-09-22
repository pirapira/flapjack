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

end Flapjack