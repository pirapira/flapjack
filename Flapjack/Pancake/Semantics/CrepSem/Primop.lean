import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.HolRef
import Flapjack.PanValues

/-!
The HOL `crepSemScript.sml` primitive operator acts on `word_lab` cells, not
the wrapper-erased raw words used by Flapjack's compatibility runtime handler.
-/

namespace Flapjack

/-- HOL `crepSem$crep_primop`: AddCarry accepts exactly three word cells and
    returns the result and carry-out as two word cells. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "crep_primop_def"]
def crepPrimopHOL {width : Nat} [NeZero width] :
    PrimOp → List (PanWordLab (BitVec width)) →
      Option (List (PanWordLab (BitVec width)))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

end Flapjack
