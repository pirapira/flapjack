import Flapjack.RiscV.L3.Defs.WritePC

/-! Literal original step PC update over the entire native state and word64 target. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "update_pc_def"]
def update_pc (v : (BitVec 64)) (s : riscv_state) : (Option riscv_state) :=
  (some («write'PC» v s))

/-- Flapjack whole option-result equation, not a distinct named HOL theorem. -/
theorem updatePC_some (v : BitVec 64) (s : riscv_state) :
    update_pc v s = some («write'PC» v s) := rfl

/-- Flapjack full-record regression derived from both source definitions, without
core bounds, successful-run premises or narrowed state. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "update_pc"]
theorem updatePC_fullRecord (v : BitVec 64) (s : riscv_state) :
    update_pc v s = some { s with c_PC := holUpdate s.procID v s.c_PC } := rfl

end Flapjack.RiscV.L3.Step
