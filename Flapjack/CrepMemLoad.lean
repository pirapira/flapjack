import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.mem_load`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:48-52`.

The source reads the memory cell only when the address belongs to
`memaddrs`; otherwise it returns `NONE`.  `crepRuntimeLoad` already has this
exact checked boundary, so this source-shaped name is an explicit alias and
does not introduce a second memory behavior.
-/

namespace Flapjack

def crepSemMemLoad (state : CrepRuntimeState α σ) (address : α) : Option α :=
  crepRuntimeLoad state address

@[simp] theorem crepSemMemLoad_eq_runtime (state : CrepRuntimeState α σ)
    (address : α) :
    crepSemMemLoad state address = crepRuntimeLoad state address := by
  rfl

end Flapjack
