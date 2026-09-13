import Flapjack.LoopSemantics

/-!
# Pancake `loopSem.get_var_imm`

Faithful executable port of `cakeml/pancake/semantics/loopSemScript.sml:165`.
Register operands read the local map; immediate operands are returned
directly.  The source uses `Word`/`word_loc`, while this layer is
parameterised by the value type used by the Loop state.
-/

namespace Flapjack

def getVarImm (state : LoopState α) : RegImm α → Option α
  | .reg name => state.locals name
  | .imm value => some value

@[simp] theorem getVarImm_reg (state : LoopState α) (name : Nat) :
    getVarImm state (.reg name) = state.locals name := by
  rfl

@[simp] theorem getVarImm_imm (state : LoopState α) (value : α) :
    getVarImm state (.imm value) = some value := by
  rfl

end Flapjack
