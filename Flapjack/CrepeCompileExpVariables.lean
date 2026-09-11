import Flapjack.Compile

namespace Flapjack

theorem loadShape_vars_mem
    [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α)
    (varName : Nat)
    (hvar : varName ∈ (loadShape address stride count value).flatMap crepExpVars) :
    varName ∈ crepExpVars value := by
  induction count generalizing address with
  | zero => cases hvar
  | succ count ih =>
      rw [loadShape] at hvar
      simp only [List.flatMap_cons, List.mem_append] at hvar
      rcases hvar with hvar | hvar
      · by_cases haddress : address == 0
        · simpa [haddress, crepExpVars, crepExpVars.crepExpVarsList] using hvar
        · simpa [haddress, crepExpVars, crepExpVars.crepExpVarsList] using hvar
      · exact ih (address + stride) hvar

theorem cexpHeads_vars_mem
    (expressions : List (List (CrepExp α))) (heads : List (CrepExp α))
    (hheads : cexpHeads expressions = some heads) (varName : Nat)
    (hvar : varName ∈ heads.flatMap crepExpVars) :
    varName ∈ expressions.flatMap (List.flatMap crepExpVars) := by
  induction expressions generalizing heads with
  | nil =>
      have hheads' : heads = [] := by
        simpa [cexpHeads] using hheads
      subst heads
      simp at hvar
  | cons expression expressions ih =>
      cases expression with
      | nil => simp [cexpHeads] at hheads
      | cons head tail =>
          cases hrest : cexpHeads expressions with
          | none => simp [cexpHeads, hrest] at hheads
          | some restHeads =>
              have hheads' : heads = head :: restHeads := by
                simpa [cexpHeads, hrest] using hheads.symm
              subst heads
              have hvar' : varName ∈ crepExpVars head ∨
                  varName ∈ restHeads.flatMap crepExpVars := by
                simpa only [List.flatMap_cons, List.mem_append] using hvar
              rcases hvar' with hvar | hvar
              · simp only [List.flatMap_cons, List.mem_append]
                exact Or.inl (Or.inl hvar)
              · have htail := ih restHeads hrest hvar
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr htail

theorem flatMap_crepExpVars_mem_take
    (expressions : List (CrepExp α)) (count : Nat) (varName : Nat)
    (hvar : varName ∈ (expressions.take count).flatMap crepExpVars) :
    varName ∈ expressions.flatMap crepExpVars := by
  induction count generalizing expressions with
  | zero => cases hvar
  | succ count ih =>
      cases expressions with
      | nil => cases hvar
      | cons expression expressions =>
          simp only [List.take_succ_cons, List.flatMap_cons, List.mem_append] at hvar ⊢
          rcases hvar with hvar | hvar
          · exact Or.inl hvar
          · exact Or.inr (ih expressions hvar)

theorem flatMap_crepExpVars_mem_drop
    (expressions : List (CrepExp α)) (count : Nat) (varName : Nat)
    (hvar : varName ∈ (expressions.drop count).flatMap crepExpVars) :
    varName ∈ expressions.flatMap crepExpVars := by
  induction count generalizing expressions with
  | zero => exact hvar
  | succ count ih =>
      cases expressions with
      | nil => cases hvar
      | cons expression expressions =>
          have htail := ih expressions hvar
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr htail

theorem compileField_vars_mem
    [OfNat α 0]
    (index : Nat) (shapes : List Shape) (expressions : List (CrepExp α))
    (varName : Nat)
    (hvar : varName ∈ (compileField index shapes expressions).1.flatMap crepExpVars) :
    varName ∈ expressions.flatMap crepExpVars := by
  induction shapes generalizing index expressions with
  | nil =>
      simp [compileField] at hvar
  | cons shape shapes ih =>
      cases index with
      | zero =>
          simpa only [compileField] using
            flatMap_crepExpVars_mem_take expressions (Shape.shapeSize shape)
              varName hvar
      | succ index =>
          have hdrop : varName ∈
              (compileField index shapes (expressions.drop (Shape.shapeSize shape))).1.flatMap
                crepExpVars := by
            simpa [compileField] using hvar
          have htail := ih index (expressions.drop (Shape.shapeSize shape)) hdrop
          exact flatMap_crepExpVars_mem_drop expressions (Shape.shapeSize shape)
            varName htail

end Flapjack
