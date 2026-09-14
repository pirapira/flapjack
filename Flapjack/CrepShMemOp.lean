import Flapjack.CrepShMemLoad
import Flapjack.CrepShMemStore

/-!
# Pancake `crepSem.sh_mem_op`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:210-219`.

The source dispatches each `Load`/`Store` width constructor to the raw-width
shared-memory transition.  Keeping the dispatch explicit preserves the source
byte counts: `Load`/`Store` use zero, `Load8`/`Store8` use one,
`Load16`/`Store16` use two, and `Load32`/`Store32` use four.
-/

namespace Flapjack

def crepShMemOp (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : CrepRuntimeStep α σ FfiFinalEvent :=
  match operator with
  | .load => crepShMemLoad state name address 0
  | .store => crepShMemStore state name address 0
  | .load8 => crepShMemLoad state name address 1
  | .store8 => crepShMemStore state name address 1
  | .load16 => crepShMemLoad state name address 2
  | .store16 => crepShMemStore state name address 2
  | .load32 => crepShMemLoad state name address 4
  | .store32 => crepShMemStore state name address 4

@[simp] theorem crepShMemOp_load (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) :
    crepShMemOp state .load name address = crepShMemLoad state name address 0 := by
  rfl

@[simp] theorem crepShMemOp_store (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) :
    crepShMemOp state .store name address = crepShMemStore state name address 0 := by
  rfl

end Flapjack
