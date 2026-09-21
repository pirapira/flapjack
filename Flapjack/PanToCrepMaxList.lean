import Flapjack.PanToCrep

/-!
Faithful executable port of HOL's `rich_list$MAX_LIST` over `num`, used by the
original Pancake `pan_to_crep` proof (`pan_to_crepProofScript.sml:4472-4482`)
to bound freshly allocated variable counters (`vmax`) and to show that a fresh
name is not already present.

Source reference: `cakeml/pancake/proofs/pan_to_crepProofScript.sml`:

    Theorem MAX_LIST_APPEND:
      MAX_LIST(a ++ b) = MAX (MAX_LIST a) (MAX_LIST b)
    Theorem MAX_LIST_NOT_MEM:
      x > MAX_LIST l ==> ~MEM x l

`maxList` mirrors `MAX_LIST [] = 0` / `MAX_LIST (h::t) = MAX h (MAX_LIST t)`.
-/

namespace Flapjack

def maxList : List Nat → Nat
  | [] => 0
  | value :: values => max value (maxList values)

theorem maxList_append (first second : List Nat) :
    maxList (first ++ second) = max (maxList first) (maxList second) := by
  induction first with
  | nil => simp [maxList]
  | cons value values ih =>
      simp only [List.cons_append, maxList, ih]
      rw [Nat.max_assoc]

theorem maxList_not_mem (bound : Nat) (values : List Nat)
    (h : bound > maxList values) : bound ∉ values := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [maxList] at h
      have hvalue : bound > value :=
        Nat.lt_of_le_of_lt (Nat.le_max_left value (maxList values)) h
      have htail : bound > maxList values :=
        Nat.lt_of_le_of_lt (Nat.le_max_right value (maxList values)) h
      simp only [List.mem_cons, not_or]
      exact ⟨by omega, ih htail⟩

end Flapjack
