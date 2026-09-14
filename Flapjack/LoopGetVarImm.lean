import Flapjack.LoopStateResult

/-!
# Pancake `loopSem.get_var_imm`

Faithful executable port of `cakeml/pancake/semantics/loopSemScript.sml:165`.
Register operands read the exact machine state's local map; immediate
operands are returned directly.  The source uses `Word`/`word_loc`, modeled by
`LoopWordLoc` here.
-/

namespace Flapjack

def getVarImm (state : LoopMachineState α) : RegImm LoopWordLoc → Option LoopWordLoc
  | .reg name => state.locals name
  | .imm value => some value

@[simp] theorem getVarImm_reg (state : LoopMachineState α) (name : Nat) :
    getVarImm state (.reg name) = state.locals name := by
  rfl

@[simp] theorem getVarImm_imm (state : LoopMachineState α) (value : LoopWordLoc) :
    getVarImm state (.imm value) = some value := by
  rfl

end Flapjack
