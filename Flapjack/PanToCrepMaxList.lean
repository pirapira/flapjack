import Flapjack.Pancake.PanToCrep

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

and `cakeml/pancake/semantics/pan_commonPropsScript.sml`:

    Theorem MAX_LIST_add_not_mem:
      ~MEM (MAX_LIST xs + 1) xs
    Theorem MAX_LIST_i_genlist:
      MAX_LIST (GENLIST I n) = n - 1

`maxList` mirrors `MAX_LIST [] = 0` / `MAX_LIST (h::t) = MAX h (MAX_LIST t)`,
`List.range n` is `GENLIST I n`.
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

theorem maxList_ge_of_mem (values : List Nat) (x : Nat) (hx : x ∈ values) :
    x ≤ maxList values := by
  induction values with
  | nil => simp at hx
  | cons value values ih =>
      simp only [maxList]
      rcases List.mem_cons.mp hx with hhead | htail
      · rw [hhead]
        exact Nat.le_max_left value (maxList values)
      · exact Nat.le_trans (ih htail) (Nat.le_max_right value (maxList values))

theorem maxList_add_one_not_mem (values : List Nat) : maxList values + 1 ∉ values := by
  induction values with
  | nil => simp
  | cons value values _ =>
      simp only [maxList, List.mem_cons, not_or]
      refine ⟨?_, ?_⟩
      · have hle := Nat.le_max_left value (maxList values)
        omega
      · intro hmem
        have hle := maxList_ge_of_mem values (max value (maxList values) + 1) hmem
        have hright := Nat.le_max_right value (maxList values)
        omega

theorem maxList_range (n : Nat) : maxList (List.range n) = n - 1 := by
  induction n with
  | zero => simp [maxList]
  | succ n ih =>
      rw [List.range_succ, maxList_append, ih]
      simp [maxList]

/-- Cake's `max_list_genlist_add_suc_val`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2579`): the maximum of
    `GENLIST (λx. SUC x + k) n` is `n + k` for `n ≠ 0`.  `List.range n` is the
    Flapjack counterpart of `GENLIST I n`. -/
theorem maxList_genlist_add_suc_val (k : Nat) :
    ∀ n, n ≠ 0 →
      maxList ((List.range n).map (fun x => (x + 1) + k)) = n + k := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ m ih =>
      intro _
      rw [List.range_succ, List.map_append, maxList_append]
      simp only [List.map_cons, List.map_nil]
      have hsingle : maxList [((m + 1) + k)] = (m + 1) + k := by
        simp only [maxList]
        exact Nat.max_eq_left (Nat.zero_le _)
      rw [hsingle]
      cases m with
      | zero =>
          simp only [List.range_zero, List.map_nil, maxList]
          exact Nat.max_eq_right (Nat.zero_le _)
      | succ m' =>
          rw [ih (by omega)]
          exact Nat.max_eq_right (by omega)

end Flapjack
