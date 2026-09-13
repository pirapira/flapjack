import Flapjack.LoopSemantics

/-!
# Pancake Loop memory load

Faithful word-valued boundary for `mem_load` from
`cakeml/pancake/semantics/loopSemScript.sml:64-69`. The original operation
checks `mdomain` before reading memory and returns `NONE` outside that domain.
The compact `LoopState` does not yet carry `mdomain`, so the exact boundary
keeps the domain explicit for later evaluator migration.
-/

namespace Flapjack

def loopMemLoad (domain : α → Bool) (memory : α → Option α)
    (address : α) : Option α :=
  if domain address then memory address else none

theorem loopMemLoad_hit (domain : α → Bool) (memory : α → Option α)
    (address : α) (inside : domain address = true) :
    loopMemLoad domain memory address = memory address := by
  simp [loopMemLoad, inside]

theorem loopMemLoad_miss (domain : α → Bool) (memory : α → Option α)
    (address : α) (outside : domain address = false) :
    loopMemLoad domain memory address = none := by
  simp [loopMemLoad, outside]

end Flapjack
