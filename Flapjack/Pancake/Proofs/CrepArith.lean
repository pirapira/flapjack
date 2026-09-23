import Flapjack.HolRef
import Flapjack.Pancake.CrepArith

/-! Exact theorem counterpart for CakeML's `crep_arithProofScript.sml`.
    The statement specializes the source's `'a word crepLang$exp` to a
    width-parametric RISC-V word, and uses the production `crepDestConst`. -/

namespace Flapjack

/-- CakeML's `dest_const_thm`: a successful destination test identifies the
    expression as exactly that constant. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm"]
theorem crepDestConst_eq_const {n : Nat} (expression : CrepExp (RiscV.Word n))
    (value : RiscV.Word n)
    (h : crepDestConst expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConst]

end Flapjack
