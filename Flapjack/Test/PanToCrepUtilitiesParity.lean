import Flapjack.Pancake.Proofs.PanToCrep

/-! Focused regressions for exact utility theorem ports from
`pan_to_crepProofScript.sml`. -/

namespace Flapjack.Test.PanToCrepUtilitiesParity

/-- HOL `filter_not_mem_self` on a concrete list. -/
theorem filter_not_mem_self_fixture :
    ([1, 2, 3] : List Nat).filter (fun x => decide (x ∉ [1, 2, 3])) = [] :=
  filter_not_mem_self [1, 2, 3]

/-- Cake `pair_map_I`: the pair constructor is identity. -/
theorem prod_mk_pair_eq_id_fixture :
    (fun p : Nat × Nat => (p.1, p.2)) = id :=
  prod_mk_pair_eq_id

/-- Cake `not_none_then_some`: non-none options have a witness. -/
theorem option_ne_none_iff_exists_fixture :
    (some 3 : Option Nat) ≠ none ↔ ∃ a, (some 3 : Option Nat) = some a :=
  option_ne_none_iff_exists (some 3)

/-- Cake `mod_eq_lt_eq`: modular equality below the modulus is equality. -/
theorem mod_eq_of_lt_eq_fixture {n x m : Nat} (hn : n < x) (hm : m < x)
    (h : n % x = m % x) : n = m :=
  mod_eq_of_lt_eq hn hm h

/-- Focused regression retaining `MAP_SOME_MEM_lemma`'s unused Nat witness. -/
theorem mapSomeMemLemma_fixture :
    ∃ (_r : Nat) (y : Nat),
      (fun n : Nat => if n == 4 then none else some (n + 1)) 3 = some y ∧
        y ∈ ([4, 6] : List Nat) :=
  mapSomeMemLemma (fun n : Nat => if n == 4 then none else some (n + 1))
    [[3], [5]] [[4], [6]] [3] 3 (by decide) (by simp) (by simp)

end Flapjack.Test.PanToCrepUtilitiesParity
