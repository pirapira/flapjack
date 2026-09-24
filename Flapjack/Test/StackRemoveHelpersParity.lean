import Flapjack.Compiler.Backend.StackRemove

/-!
# `stack_remove` compiler value-helper parity

Kernel-checked Lean regression for the state-free value helpers ported from
`cakeml/compiler/backend/stack_removeScript.sml` (direct HOL EVAL oracle
`scripts/hol-probes/stack_remove_helpers_probe.out`).
-/

namespace Flapjack.Test.StackRemoveHelpersParity

open Flapjack
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- `max_stack_alloc` is `255`. -/
example : maxStackAlloc = 255 := rfl

/-- `word_offset` at width 8 for 3 is `3w` (HOL row `word_offset_3_8`). -/
example : wordOffset (width := 8) 3 = (3 : BitVec 8) := rfl

/-- `word_offset` at width 64 for 3 is `24w` (HOL row `word_offset_3_64`). -/
example : wordOffset (width := 64) 3 = (24 : BitVec 64) := rfl

/-- `store_list` has 48 entries (HOL row `store_list_len`). -/
example : storeList.length = 48 := rfl

/-- `store_list` starts with `NextFree` (HOL row `store_list_head`). -/
example : storeList.head? = some (.nextFree : StoreName) := rfl

/-- `store_list` ends with `Temp 31w` (HOL row `store_list_last`). -/
example : storeList.getLast? = some (.temp (BitVec.ofNat 5 31) : StoreName) := rfl

/-- `store_list` has even length, so `store_length` is the length (HOL row `store_length`). -/
example : storeLength = 48 := rfl

/-- `stack_err_lab` is `2` (HOL row `stack_err_lab`). -/
example : stackErrLab = 2 := rfl

/-- Executable mirror of the eight oracle rows. -/
def storeListHeadIsNextFree : Bool :=
  match storeList with
  | .nextFree :: _ => true
  | _ => false

def storeListLastIsTemp31 : Bool :=
  match storeList.reverse with
  | .temp value :: _ => value == BitVec.ofNat 5 31
  | _ => false

def helpersGuard : Bool :=
  (maxStackAlloc == 255) &&
  (wordOffset (width := 8) 3 == (3 : BitVec 8)) &&
  (wordOffset (width := 64) 3 == (24 : BitVec 64)) &&
  (storeList.length == 48) &&
  storeListHeadIsNextFree &&
  storeListLastIsTemp31 &&
  (storeLength == 48) &&
  (stackErrLab == 2)

#guard helpersGuard

/-- Prints the parity line and returns the guard. -/
def runChecks : IO Bool := do
  IO.println "PASS stack_remove compiler value helpers match all 8 oracle rows"
  pure helpersGuard

end Flapjack.Test.StackRemoveHelpersParity