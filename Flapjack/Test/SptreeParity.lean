import Flapjack.Misc.Sptree

/-!
Regression pinning `Misc.Sptree` (the exact `spt`/`num_set` carrier) against the
direct HOL oracle `scripts/hol-probes/num_set_spt_probe.out`.
-/

namespace Flapjack.Test.SptreeParity

open Flapjack

/-- The empty `num_set`. -/
private def emptyTree : NumSet := .ln

/-- One element (`0`) inserted into the empty set. -/
private def zeroInserted : NumSet := sptInsert 0 () emptyTree

/-- Two elements (`0` then `1`) inserted into the empty set. -/
private def twoInserted : NumSet := sptInsert 1 () zeroInserted

-- 1. `lookup_ln`
example : sptLookup 0 emptyTree = none := by simp [emptyTree]
-- 2. `insert0`
example : sptInsert 0 () emptyTree = .ls () := by simp [emptyTree]
-- 3. `lookup_ins0`
example : sptLookup 0 zeroInserted = some () := by simp [zeroInserted, emptyTree, sptLookup]
-- 4. `lookup_ins1_0`
example : sptLookup 0 twoInserted = some () := by simp [twoInserted, zeroInserted, emptyTree, sptInsert, sptLookup]
-- 5. `lookup_ins_other`
example : sptLookup 5 (sptInsert 2 () emptyTree) = none := by simp [emptyTree, sptInsert, sptLookup]
-- 6. `insert1_shape`
example : sptInsert 1 () emptyTree = .bn .ln (.ls ()) := by simp [emptyTree, sptInsert]
-- 7. `insert2_shape`
example : sptInsert 2 () emptyTree = .bn (.ls ()) .ln := by simp [emptyTree, sptInsert]
-- 8. `wf_ins`
example : sptWf twoInserted = true := by simp [twoInserted, zeroInserted, emptyTree, sptInsert, sptIsEmpty, sptWf]
-- 9. `isempty_ln`
example : sptIsEmpty emptyTree = true := by simp [emptyTree, sptIsEmpty]
-- 10. `isempty_ins`
example : sptIsEmpty zeroInserted = false := by simp [zeroInserted, emptyTree, sptIsEmpty]
-- 11. `insert_ovw`
example : sptLookup 0 (sptInsert 0 () zeroInserted) = some () := by simp [zeroInserted, emptyTree, sptInsert, sptLookup]

/-- Executable mirror of the oracle rows for `#guard`. -/
private def sptreeGuard : Bool :=
  (sptLookup 0 emptyTree == none) &&
    (sptInsert 0 () emptyTree == .ls ()) &&
    (sptLookup 0 zeroInserted == some ()) &&
    (sptLookup 0 twoInserted == some ()) &&
    (sptLookup 5 (sptInsert 2 () emptyTree) == none) &&
    (sptInsert 1 () emptyTree == .bn .ln (.ls ())) &&
    (sptInsert 2 () emptyTree == .bn (.ls ()) .ln) &&
    (sptWf twoInserted == true) &&
    (sptIsEmpty emptyTree == true) &&
    (sptIsEmpty zeroInserted == false) &&
    (sptLookup 0 (sptInsert 0 () zeroInserted) == some ())

#eval sptreeGuard
#guard sptreeGuard

/-- The oracle lookup/insert lemma for key `0` also holds for an arbitrary tree. -/
example (value : Unit) (tree : NumSet) : sptLookup 0 (sptInsert 0 value tree) = some value :=
  sptLookup_sptInsert_zero value tree

def runChecks : IO Bool := do
  IO.println "PASS exact spt/num_set carrier lookup/insert/wf match all 11 oracle rows"
  pure sptreeGuard

end Flapjack.Test.SptreeParity