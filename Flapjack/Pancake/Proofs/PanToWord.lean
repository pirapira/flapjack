import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.Semantics.PanProps

/-!
The source-level lemmas from CakeML's `pan_to_wordProofScript.sml`.
This is the counterpart module for theorem ports from that HOL proof script.
-/

namespace Flapjack

/-- Exact port of HOL `pan_exps_of_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1018`).  Enumerating
    the expressions of a nested sequence is the concatenation of the
    per-statement expression lists.  This is a concrete proof consumer of the
    exact PanProps `expsOfHOL` port. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_exps_of_nested_seq"]
theorem panExpsOfNestedSeqHOL {width : Nat} [NeZero width]
    (statements : List (Flapjack.Pancake.PanLang.ProgHOL width)) :
    expsOfHOL (Flapjack.Pancake.PanLang.nestedSeqHOL statements) =
      (statements.map expsOfHOL).flatten := by
  induction statements with
  | nil => rfl
  | cons statement statements ih =>
      simp only [Flapjack.Pancake.PanLang.nestedSeqHOL, expsOfHOL, List.map_cons,
        List.flatten_cons, ih]

end Flapjack
