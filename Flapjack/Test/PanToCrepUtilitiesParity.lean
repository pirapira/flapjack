import Flapjack.Pancake.Proofs.PanToCrep

/-! Focused regressions for exact utility theorem ports from
`pan_to_crepProofScript.sml`. -/

namespace Flapjack.Test.PanToCrepUtilitiesParity

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

end Flapjack.Test.PanToCrepUtilitiesParity
