import Flapjack.Compiler.Backend.RegAlloc

/-! Parity checks for the CakeML register-allocation partition predicates and
the partition lemma, matched against the direct HOL EVAL oracle
`scripts/hol-probes/reg_alloc_var_partition_probe.out`. -/

namespace Flapjack.Test.RegAllocVarParity

open Flapjack

private def partitionsOk (n : Nat) : Bool :=
  (isStackVar n == (!isPhyVar n && !isAllocVar n)) &&
  (isPhyVar n == (!isStackVar n && !isAllocVar n)) &&
  (isAllocVar n == (!isPhyVar n && !isStackVar n))

-- Predicate rows from the HOL oracle.
example : isPhyVar 6 = true := by decide
example : isPhyVar 7 = false := by decide
example : isStackVar 7 = true := by decide
example : isStackVar 6 = false := by decide
example : isAllocVar 5 = true := by decide
example : isAllocVar 4 = false := by decide

-- Partition rows from the HOL oracle.
example : partitionsOk 3 = true := by decide
example : partitionsOk 2 = true := by decide
example : partitionsOk 1 = true := by decide
example : partitionsOk 0 = true := by decide

-- The tagged HOL theorem, instantiated.
example (n : Nat) : (isStackVar n ↔ ¬ isPhyVar n ∧ ¬ isAllocVar n) :=
  (conventionPartitions n).1

private def guards : List Bool :=
  [isPhyVar 6, isPhyVar 7, isStackVar 7, isStackVar 6, isAllocVar 5,
   isAllocVar 4, partitionsOk 3, partitionsOk 2, partitionsOk 1, partitionsOk 0]

private def expected : List Bool :=
  [true, false, true, false, true, false, true, true, true, true]

#guard guards == expected

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS reg_alloc is_phy_var/is_stack_var/is_alloc_var and convention_partitions match all 10 oracle rows"
  else
    IO.println "FAIL reg_alloc partition parity"
  pure (guards == expected)

end Flapjack.Test.RegAllocVarParity