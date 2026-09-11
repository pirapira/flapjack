import Flapjack.Compile

namespace Flapjack

theorem compileParamVars_offset_le_next
    (params : List (VarName × Shape)) (offset : Nat) :
    offset ≤ (compileParamVars params offset).2.snd := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars]
          have hnext : offset + Shape.shapeSize shape ≤
              (compileParamVars params (offset + Shape.shapeSize shape)).2.snd :=
            ih (offset + Shape.shapeSize shape)
          calc
            offset ≤ offset + Shape.shapeSize shape := by omega
            _ ≤ (compileParamVars params (offset + Shape.shapeSize shape)).2.snd := hnext

theorem compileParamVars_slot_lt
    (params : List (VarName × Shape)) (offset : Nat)
    (name : VarName) (shape : Shape) (names : List Nat)
    (hlookup : lookupInfo name (compileParamVars params offset).1 =
      some (shape, names)) :
    ∀ slot ∈ names, slot < (compileParamVars params offset).2.snd := by
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
            rcases List.mem_map.1 hslot with ⟨index, hindex, rfl⟩
            have hslotRange : offset + index <
                offset + Shape.shapeSize parameterShape := by
              exact Nat.add_lt_add_left (List.mem_range.1 hindex) offset
            have hnext := compileParamVars_offset_le_next params
              (offset + Shape.shapeSize parameterShape)
            change offset + index <
              (compileParamVars params (offset + Shape.shapeSize parameterShape)).2.snd
            exact Nat.lt_of_lt_of_le hslotRange hnext
          · simp [hname] at hlookup
            have htail := ih (offset + Shape.shapeSize parameterShape)
              hlookup
            intro slot hslot
            exact htail slot hslot

theorem compileParamVars_slot_le
    (params : List (VarName × Shape)) (offset : Nat)
    (name : VarName) (shape : Shape) (names : List Nat)
    (hlookup : lookupInfo name (compileParamVars params offset).1 =
      some (shape, names)) :
    ∀ slot ∈ names, slot ≤ (compileParamVars params offset).2.snd := by
  intro slot hslot
  exact Nat.le_of_lt (compileParamVars_slot_lt params offset name shape names
    hlookup slot hslot)

end Flapjack
