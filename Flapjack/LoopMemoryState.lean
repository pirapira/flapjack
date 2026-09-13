import Flapjack.LoopMemLoad
import Flapjack.LoopMemStore

/-!
# Exact Loop word-memory adapter

The original `loopSem$state` carries both a word memory and `mdomain`.  The
legacy compact `LoopState` intentionally omits the domain, so the exact
memory equations cannot be routed through it without changing many dependent
proofs at once.  This small adapter makes the original state boundary
explicit and is the migration point for those proofs.
-/

namespace Flapjack

structure LoopMemoryState (α : Type u) where
  memory : α → Option α
  domain : α → Bool

def loopMemoryLoad (state : LoopMemoryState α) (address : α) : Option α :=
  loopMemLoad state.domain state.memory address

def loopMemoryStore [BEq α] (state : LoopMemoryState α)
    (address value : α) : Option (LoopMemoryState α) :=
  (loopMemStore state.domain state.memory address value).map
    (fun memory => { state with memory := memory })

theorem loopMemoryLoad_eq (state : LoopMemoryState α) (address : α) :
    loopMemoryLoad state address =
      if state.domain address then state.memory address else none := by
  rfl

theorem loopMemoryStore_outside [BEq α] (state : LoopMemoryState α)
    (address value : α) (outside : state.domain address = false) :
    loopMemoryStore state address value = none := by
  simp [loopMemoryStore, loopMemStore, outside]

end Flapjack
