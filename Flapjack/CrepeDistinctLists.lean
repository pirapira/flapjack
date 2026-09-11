import Flapjack.Crepe

/-!
The compiler's `distinctLists` guard is exactly the non-interference property
needed by flattened assignment evaluation: no destination slot occurs in any
right-hand-side expression.
-/

namespace Flapjack

theorem distinctLists_flatMap_not_mem
    (slots : List Nat) (expressions : List (CrepExp α))
    (hdistinct : distinctLists slots (expressions.flatMap crepExpVars) = true) :
    ∀ slot ∈ slots, ∀ expression ∈ expressions,
      slot ∉ crepExpVars expression := by
  simp [distinctLists, List.all_eq_true] at hdistinct
  intro slot hslot expression hexpression hslotExpression
  exact hdistinct slot hslot expression hexpression hslotExpression

end Flapjack
