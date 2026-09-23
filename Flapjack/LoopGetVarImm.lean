import Flapjack.LoopStateResult

/-!
# Pancake `loopSem.get_var_imm`

Faithful executable port of `cakeml/pancake/semantics/loopSemScript.sml:165`.
Register operands read the exact machine state's local map; immediate
operands are returned directly.  The source uses `Word`/`word_loc`, modeled by
`LoopValue` here.
-/

namespace Flapjack

def getVarImm (state : LoopMachineState W F) : RegImm (LoopValue W) → Option (LoopValue W)
  | .reg name => state.locals name
  | .imm value => some value

@[simp] theorem getVarImm_reg (state : LoopMachineState W F) (name : Nat) :
    getVarImm state (.reg name) = state.locals name := by
  rfl

@[simp] theorem getVarImm_imm (state : LoopMachineState W F) (value : LoopValue W) :
    getVarImm state (.imm value) = some value := by
  rfl

end Flapjack