import Flapjack.CompileParamVarsBounds

/-!
Lower bounds for slots allocated by `compileParamVars`.

The upper bound is already used by expression freshness proofs.  The lower
bound is the complementary fact needed to show that source-order formal
parameter ranges are disjoint from the ranges allocated to their prefix.
-/

namespace Flapjack

theorem compileParamVars_slot_ge
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat)
    (name : VarName) (shape : Shape) (names : List Nat)
    (hlookup : lookupInfo name (compileParamVars params offset).1 =
      some (shape, names)) :
    ∀ slot ∈ names, offset ≤ slot := by
  induction params generalizing offset with
  | nil =>
      simp [compileParamVars, lookupInfo] at hlookup
  | cons param params ih =>
      cases param with
      | mk parameterName parameterShape =>
          simp only [compileParamVars] at hlookup ⊢
          change (if parameterName == name then
              some (parameterShape,
                (List.range (Shape.shapeSize parameterShape)).map
                  (fun index => offset + index))
            else lookupInfo name
              (compileParamVars params (offset + Shape.shapeSize parameterShape)).1) =
              some (shape, names) at hlookup
          by_cases hname : (parameterName == name) = true
          · simp [hname] at hlookup
            rcases hlookup with ⟨hshape, hnames⟩
            subst shape
            subst names
            intro slot hslot
            rcases List.mem_map.mp hslot with ⟨index, hindex, rfl⟩
            exact Nat.le_add_right offset index
          · simp [hname] at hlookup
            have htail := ih (offset + Shape.shapeSize parameterShape)
              hlookup
            intro slot hslot
            exact Nat.le_trans
              (by omega : offset ≤ offset + Shape.shapeSize parameterShape)
              (htail slot hslot)

end Flapjack
