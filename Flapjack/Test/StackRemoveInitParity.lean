import Flapjack.Compiler.Backend.StackRemove

/-!
Parity test for the stack_remove `make_init` prerequisites ported in
`Flapjack/Compiler/Backend/StackRemove.lean`:
`is_SOME_Word`, `read_mem`/`LENGTH_read_mem`, `addresses`/`IN_addresses`
(plus `wordLang$word_loc`).  The expected observations are the direct HOL
`EVAL` rows in `scripts/hol-probes/stack_remove_init_probe.out`.
-/

namespace Flapjack.Test.StackRemoveInitParity

open Flapjack
open Flapjack.Compiler.Backend.StackRemove

private abbrev W := BitVec 8

private def headIs3 : Bool :=
  (readMem (2 : W) (fun x => WordLoc.word (x + 1)) 3).head? ==
    some (WordLoc.word (3 : W))

/-- The `is_SOME_Word` and `read_mem` oracle rows. -/
private def parityGuard : Bool :=
  (isSomeWord (some (WordLoc.word (7 : W))) == true) &&
  (isSomeWord (some (WordLoc.loc 1 2) : Option (WordLoc W)) == false) &&
  (isSomeWord (none : Option (WordLoc W)) == false) &&
  ((readMem (0 : W) (fun x => WordLoc.word x) 3).length == 3) &&
  headIs3

example : isSomeWord (some (WordLoc.word (7 : W))) = true := by decide
example : isSomeWord (some (WordLoc.loc 1 2) : Option (WordLoc W)) = false := by decide
example : isSomeWord (none : Option (WordLoc W)) = false := by decide
example : (readMem (0 : W) (fun x => WordLoc.word x) 3).length = 3 :=
  length_readMem 3 0 _
example : (readMem (2 : W) (fun x => WordLoc.word (x + 1)) 3).head? =
    some (WordLoc.word (3 : W)) := by simp only [readMem, bytesInWord, BitVec.ofNat_eq_ofNat]; decide
example : addresses (0 : W) 3 (0 : W) := by simp only [addresses]; decide
example : addresses (0 : W) 3 (2 : W) := by simp only [addresses]; decide
example : ¬ addresses (0 : W) 3 (5 : W) := by simp only [addresses]; decide

example : addresses (0 : W) 3 (2 : W) ↔
    ∃ i, i < 3 ∧ (2 : W) = 0 + BitVec.ofNat 8 i * bytesInWord 8 :=
  mem_addresses 3 0 2

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS stack_remove make_init prerequisites match all 8 oracle rows"
  else
    IO.println "FAIL stack_remove make_init prerequisites"
  pure parityGuard

end Flapjack.Test.StackRemoveInitParity