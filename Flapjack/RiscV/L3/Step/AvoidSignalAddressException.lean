import Flapjack.RiscV.L3.Defs.AddressException

/-! `avoid_signalAddressException`: the original step theory's observation that a
false guard leaves the state unchanged. HOL `riscv_stepScript.sml:553-557` proves
`~b ==> ((if b then signalAddressException t u else s) = s)` for the model
`signalAddressException` (`Flapjack/RiscV/L3/Defs/AddressException.lean`, HOL
`riscvScript.sml:3460-3472`). The Lean statement keeps the original binders and
the pair-typed exception argument; no premise beyond the original guard is added. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "avoid_signalAddressException"]
theorem avoidSignalAddressException (b : Bool) (t : (ExceptionType × (BitVec 64)))
    (u s : riscv_state) :
    (¬ b) → ((if b then signalAddressException t u else s) = s) := by
  intro hb
  rw [if_neg hb]

end Flapjack.RiscV.L3.Step
