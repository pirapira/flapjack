import Flapjack.Language

/-!
# Pancake `panSem.nb_op`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:549-553`.

This is the source-shaped byte-width mapping used by Pancake's shared-memory
operators.  Word-sized operations use zero to preserve the source convention.
-/

namespace Flapjack

def panNbOp : OpSize → Nat
  | .op8 => 1
  | .op16 => 2
  | .opW => 0
  | .op32 => 4

@[simp] theorem panNbOp_op8 : panNbOp .op8 = 1 := by rfl

@[simp] theorem panNbOp_op16 : panNbOp .op16 = 2 := by rfl

@[simp] theorem panNbOp_opW : panNbOp .opW = 0 := by rfl

@[simp] theorem panNbOp_op32 : panNbOp .op32 = 4 := by rfl

end Flapjack
