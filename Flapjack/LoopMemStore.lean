import Flapjack.LoopSemantics

/-!
# Pancake Loop memory store

Faithful word-valued boundary for `mem_store` from
`cakeml/pancake/semantics/loopSemScript.sml:57-62`.  The original operation
checks `mdomain` before updating memory and returns `NONE` outside that domain.
The compact `LoopState` does not yet carry `mdomain`, so this boundary keeps
the domain explicit; the exact-state migration can route the full evaluator
through it later.
-/

namespace Flapjack

def loopMemStore [BEq α] (domain : α → Bool) (memory : α → Option α)
    (address value : α) : Option (α → Option α) :=
  if domain address then
    some (updateLoopMemory memory address value)
  else none

theorem loopMemStore_hit [BEq α] [LawfulBEq α]
    (domain : α → Bool) (memory : α → Option α)
    (address value : α) (inside : domain address = true) :
    (loopMemStore domain memory address value).map (fun updated => updated address) =
      some value := by
  simp [loopMemStore, inside, updateLoopMemory]

theorem loopMemStore_miss [BEq α] (domain : α → Bool) (memory : α → Option α)
    (address value : α) (outside : domain address = false) :
    loopMemStore domain memory address value = none := by
  simp [loopMemStore, outside]

end Flapjack
