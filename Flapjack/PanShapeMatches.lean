import Flapjack.PanValues

/-!
Transitivity of the shape relation used by the source assignment evaluator.
The evaluator checks the new value against the old value, while the Crep
state relation checks the old value against the compiler shape.  This bridge
allows those two checks to be composed.
-/

namespace Flapjack

mutual
  theorem panShapeMatches_trans
      [LawfulBEq String]
      (left middle right : Shape)
      (hleft : panShapeMatches left middle = true)
      (hmiddle : panShapeMatches middle right = true) :
      panShapeMatches left right = true := by
    cases left with
    | one =>
        cases middle <;> cases right <;>
          simp [panShapeMatches] at hleft hmiddle ⊢
        all_goals exact hleft.trans hmiddle
    | named leftName =>
        cases middle <;> cases right <;>
          simp [panShapeMatches] at hleft hmiddle ⊢
        all_goals exact hleft.trans hmiddle
    | comb leftFields =>
        cases middle with
        | one => simp [panShapeMatches] at hleft
        | named middleName => simp [panShapeMatches] at hleft
        | comb middleFields =>
            cases right with
            | one => simp [panShapeMatches] at hmiddle
            | named rightName => simp [panShapeMatches] at hmiddle
            | comb rightFields =>
                simp only [panShapeMatches] at hleft hmiddle ⊢
                exact panShapeListMatches_trans leftFields middleFields rightFields
                  hleft hmiddle
  theorem panShapeListMatches_trans
      [LawfulBEq String]
      (left middle right : List Shape)
      (hleft : panShapeMatches.panShapeListMatches left middle = true)
      (hmiddle : panShapeMatches.panShapeListMatches middle right = true) :
      panShapeMatches.panShapeListMatches left right = true := by
    cases left with
    | nil =>
        cases middle <;> cases right <;>
          simp [panShapeMatches.panShapeListMatches] at hleft hmiddle ⊢
    | cons leftHead leftTail =>
        cases middle with
        | nil => simp [panShapeMatches.panShapeListMatches] at hleft
        | cons middleHead middleTail =>
            cases right with
            | nil => simp [panShapeMatches.panShapeListMatches] at hmiddle
            | cons rightHead rightTail =>
                simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true]
                  at hleft hmiddle ⊢
                exact ⟨panShapeMatches_trans leftHead middleHead rightHead
                  hleft.1 hmiddle.1,
                  panShapeListMatches_trans leftTail middleTail rightTail
                    hleft.2 hmiddle.2⟩
end

end Flapjack
