import Flapjack.HolRef

/-! Exact source counterpart of the CakeML register-allocation partition
predicates and their partition lemma
(`cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1132-1145`).
`is_stack_var`, `is_phy_var`, and `is_alloc_var` classify a register number by
its residue modulo four; `convention_partitions` states that each class is
exactly the complement of the other two. -/

namespace Flapjack

/-- HOL `reg_alloc$is_stack_var` (`reg_allocScript.sml:1132-1134`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_stack_var_def"]
def isStackVar (n : Nat) : Bool := n % 4 = 3

/-- HOL `reg_alloc$is_phy_var` (`reg_allocScript.sml:1135-1137`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_phy_var_def"]
def isPhyVar (n : Nat) : Bool := n % 2 = 0

/-- HOL `reg_alloc$is_alloc_var` (`reg_allocScript.sml:1138-1140`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_alloc_var_def"]
def isAllocVar (n : Nat) : Bool := n % 4 = 1

/-- HOL `reg_alloc$convention_partitions` (`reg_allocScript.sml:1142-1151`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "convention_partitions"]
theorem conventionPartitions (n : Nat) :
    (isStackVar n ↔ ¬ isPhyVar n ∧ ¬ isAllocVar n) ∧
    (isPhyVar n ↔ ¬ isStackVar n ∧ ¬ isAllocVar n) ∧
    (isAllocVar n ↔ ¬ isPhyVar n ∧ ¬ isStackVar n) := by
  have hmod : n % 2 = (n % 4) % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have := Nat.mod_lt n (by decide : 0 < 4); omega
  rcases h4 with h | h | h | h <;>
    (rw [isStackVar, isPhyVar, isAllocVar, hmod, h]; decide)

end Flapjack