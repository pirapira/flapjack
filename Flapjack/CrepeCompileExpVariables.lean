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

theorem flatMap_crepExpVars_map_var_mem
    {α : Type u}
    (names : List Nat) (varName : Nat)
    (hvar : varName ∈ (names.map (CrepExp.var : Nat → CrepExp α)).flatMap
      crepExpVars) :
    varName ∈ names := by
  induction names with
  | nil => cases hvar
  | cons name names ih =>
      have hvar' : varName ∈ crepExpVars (.var name : CrepExp α) ∨
          varName ∈ (names.map (CrepExp.var : Nat → CrepExp α)).flatMap
            crepExpVars := by
        simpa only [List.map, List.flatMap_cons, List.mem_append] using hvar
      rcases hvar' with hvar | hvar
      · simp only [crepExpVars] at hvar
        simp only [List.mem_cons]
        exact Or.inl (by simpa using hvar)
      · simp only [List.mem_cons]
        exact Or.inr (ih hvar)

theorem flatMap_fst_crepExpVars_eq
    (compiled : List (List (CrepExp α) × Shape)) :
    (compiled.flatMap Prod.fst).flatMap crepExpVars =
      compiled.flatMap (fun entry => entry.1.flatMap crepExpVars) := by
  exact List.flatMap_assoc

theorem flatMap_map_fst_crepExpVars_eq
    (compiled : List (List (CrepExp α) × Shape)) :
    (compiled.map Prod.fst).flatMap (List.flatMap crepExpVars) =
      compiled.flatMap (fun entry => entry.1.flatMap crepExpVars) := by
  rw [List.flatMap_map]

theorem crepExpVarsList_eq_flatMap
    (expressions : List (CrepExp α)) :
    crepExpVars.crepExpVarsList expressions = expressions.flatMap crepExpVars := by
  induction expressions with
  | nil => simp [crepExpVars.crepExpVarsList]
  | cons expression expressions ih =>
      simp [crepExpVars.crepExpVarsList, ih]

theorem compileExp_vars_bounded
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α)
    (hbound : ∀ name shape names,
      lookupInfo name context.vars = some (shape, names) →
      ∀ varName ∈ names, varName ≤ context.maxVar)
    (expression : Exp α) :
    ∀ varName ∈ (compileExp context expression).1.flatMap crepExpVars,
      varName ≤ context.maxVar := by
  have hmain : ∀ n (expression : Exp α), sizeOf expression = n →
      ∀ varName ∈ (compileExp context expression).1.flatMap crepExpVars,
        varName ≤ context.maxVar := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro expression hsize
        have hlistBound : ∀ sourceExpressions,
            (∀ sourceExpression ∈ sourceExpressions,
              sizeOf sourceExpression < n) →
            ∀ varName ∈
              (compileExp.compileExpList context sourceExpressions).flatMap
                (fun compiled => compiled.1.flatMap crepExpVars),
              varName ≤ context.maxVar := by
          intro sourceExpressions
          induction sourceExpressions with
          | nil =>
              intro _
              simp [compileExp.compileExpList]
          | cons sourceExpression sourceExpressions ihFields =>
              intro hsourceSmall
              have hhead := ih (sizeOf sourceExpression)
                (hsourceSmall sourceExpression (by simp)) sourceExpression rfl
              have htail := ihFields
                (fun current hcurrent =>
                  hsourceSmall current (by simp [hcurrent]))
              simp only [compileExp.compileExpList, List.flatMap_cons,
                List.mem_append]
              intro varName hvar
              rcases hvar with hvar | hvar
              · exact hhead varName hvar
              · exact htail varName hvar
        cases expression with
        | const value => simp [compileExp]
        | var kind name =>
            by_cases hlocal : kind = VarKind.local
            · subst kind
              cases hlookup : lookupInfo name context.vars with
              | none => simp [compileExp, hlookup]
              | some info =>
                  cases info with
                  | mk shape names =>
                      intro varName hvar
                      have hvar0 : varName ∈
                          (names.map (CrepExp.var : Nat → CrepExp α)).flatMap
                            crepExpVars := by
                        simpa [compileExp, hlookup] using hvar
                      have hvar' := flatMap_crepExpVars_map_var_mem
                        (α := α) names varName hvar0
                      exact hbound name shape names hlookup varName hvar'
            · have hglobal : kind = VarKind.global := by
                cases kind <;> simp_all
              subst kind
              simp [compileExp]
        | rStruct fields =>
            have hsmall : ∀ field ∈ fields, sizeOf field < n := by
              intro field hmem
              rw [← hsize]
              decreasing_trivial
            intro varName hvar
            have hvar0 : varName ∈
                ((compileExp.compileExpList context fields).flatMap Prod.fst).flatMap
                  crepExpVars := by
              simpa only [compileExp] using hvar
            rw [flatMap_fst_crepExpVars_eq] at hvar0
            exact hlistBound fields hsmall varName hvar0
        | rField index value =>
            cases hcompiled : compileExp context value with
            | mk expressions resultShape =>
                cases resultShape with
                | one => simp [compileExp, hcompiled]
                | named name => simp [compileExp, hcompiled]
                | comb shapes =>
                    intro varName hvar
                    have hfield : varName ∈
                        (compileField index shapes expressions).1.flatMap
                          crepExpVars := by
                      simpa [compileExp, hcompiled] using hvar
                    have hvalueSmall : sizeOf value < n := by
                      rw [← hsize]
                      decreasing_trivial
                    have hvalue := ih (sizeOf value) hvalueSmall value rfl
                    have hsource := compileField_vars_mem index shapes
                      expressions varName hfield
                    apply hvalue
                    simpa [hcompiled] using hsource
        | nStruct name fields => simp [compileExp]
        | nField name value => simp [compileExp]
        | load shape address =>
            cases hcompiled : compileExp context address with
            | mk expressions resultShape =>
                cases expressions with
                | nil => simp [compileExp, hcompiled]
                | cons first rest =>
                    intro varName hvar
                    have hloadInput : varName ∈
                        (loadShape 0 context.bytesInWord (Shape.shapeSize shape) first).flatMap
                          crepExpVars := by
                      simpa only [compileExp, hcompiled] using hvar
                    have hload := loadShape_vars_mem 0 context.bytesInWord
                      (Shape.shapeSize shape) first varName hloadInput
                    have haddressSmall : sizeOf address < n := by
                      rw [← hsize]
                      decreasing_trivial
                    have haddress := ih (sizeOf address) haddressSmall address rfl
                    apply haddress
                    rw [hcompiled]
                    simp only [List.flatMap_cons, List.mem_append]
                    exact Or.inl hload
        | load32 address =>
            cases hcompiled : compileExp context address with
            | mk expressions resultShape =>
                cases expressions with
                | nil => simp [compileExp, hcompiled]
                | cons first rest =>
                    cases resultShape with
                    | one =>
                        intro varName hvar
                        have hsource : varName ∈ crepExpVars first := by
                          simpa only [compileExp, hcompiled, List.flatMap_cons,
                            List.flatMap_nil, List.mem_append, List.not_mem_nil,
                            or_false,
                            crepExpVars] using hvar
                        have haddressSmall : sizeOf address < n := by
                          rw [← hsize]
                          decreasing_trivial
                        have haddress := ih (sizeOf address) haddressSmall address rfl
                        apply haddress
                        rw [hcompiled]
                        simp only [List.flatMap_cons, List.mem_append]
                        exact Or.inl hsource
                    | named name => simp [compileExp, hcompiled]
                    | comb shapes => simp [compileExp, hcompiled]
        | loadByte address =>
            cases hcompiled : compileExp context address with
            | mk expressions resultShape =>
                cases expressions with
                | nil => simp [compileExp, hcompiled]
                | cons first rest =>
                    cases resultShape with
                    | one =>
                        intro varName hvar
                        have hsource : varName ∈ crepExpVars first := by
                          simpa only [compileExp, hcompiled, List.flatMap_cons,
                            List.flatMap_nil, List.mem_append, List.not_mem_nil,
                            or_false,
                            crepExpVars] using hvar
                        have haddressSmall : sizeOf address < n := by
                          rw [← hsize]
                          decreasing_trivial
                        have haddress := ih (sizeOf address) haddressSmall address rfl
                        apply haddress
                        rw [hcompiled]
                        simp only [List.flatMap_cons, List.mem_append]
                        exact Or.inl hsource
                    | named name => simp [compileExp, hcompiled]
                    | comb shapes => simp [compileExp, hcompiled]
        | op operator args =>
            cases hheads : cexpHeads
                ((compileExp.compileExpList context args).map Prod.fst) with
            | none => simp [compileExp, hheads]
            | some heads =>
                intro varName hvar
                have hheadsVar : varName ∈ heads.flatMap crepExpVars := by
                  simpa only [compileExp, hheads, List.flatMap_cons,
                    List.flatMap_nil, List.mem_append, List.not_mem_nil,
                    or_false, crepExpVars, crepExpVars.crepExpVarsList,
                    crepExpVarsList_eq_flatMap] using hvar
                have hsource := cexpHeads_vars_mem
                  ((compileExp.compileExpList context args).map Prod.fst)
                  heads hheads varName hheadsVar
                have hsmall : ∀ arg ∈ args, sizeOf arg < n := by
                  intro arg harg
                  rw [← hsize]
                  decreasing_trivial
                have hsource' : varName ∈
                    (compileExp.compileExpList context args).flatMap
                      (fun entry => entry.1.flatMap crepExpVars) := by
                  rw [← flatMap_map_fst_crepExpVars_eq]
                  exact hsource
                exact hlistBound args hsmall varName hsource'
        | panOp operator args =>
            cases hheads : cexpHeads
                ((compileExp.compileExpList context args).map Prod.fst) with
            | none => simp [compileExp, hheads]
            | some heads =>
                intro varName hvar
                have hheadsVar : varName ∈ heads.flatMap crepExpVars := by
                  simpa only [compileExp, hheads, List.flatMap_cons,
                    List.flatMap_nil, List.mem_append, List.not_mem_nil,
                    or_false, crepExpVars, crepExpVars.crepExpVarsList,
                    crepExpVarsList_eq_flatMap] using hvar
                have hsource := cexpHeads_vars_mem
                  ((compileExp.compileExpList context args).map Prod.fst)
                  heads hheads varName hheadsVar
                have hsmall : ∀ arg ∈ args, sizeOf arg < n := by
                  intro arg harg
                  rw [← hsize]
                  decreasing_trivial
                have hsource' : varName ∈
                    (compileExp.compileExpList context args).flatMap
                      (fun entry => entry.1.flatMap crepExpVars) := by
                  rw [← flatMap_map_fst_crepExpVars_eq]
                  exact hsource
                exact hlistBound args hsmall varName hsource'
        | cmp operator left right =>
            cases hleft : compileExp context left with
            | mk leftExpressions leftShape =>
                cases hright : compileExp context right with
                | mk rightExpressions rightShape =>
                    cases leftExpressions with
                    | nil => simp [compileExp, hleft, hright]
                    | cons leftHead leftTail =>
                        cases rightExpressions with
                        | nil => simp [compileExp, hleft, hright]
                        | cons rightHead rightTail =>
                            intro varName hvar
                            have hvar' : varName ∈ crepExpVars leftHead ∨
                                varName ∈ crepExpVars rightHead := by
                              simpa only [compileExp, hleft, hright,
                                List.flatMap_cons, List.flatMap_nil,
                                List.mem_append, List.not_mem_nil, or_false,
                                crepExpVars,
                                List.mem_append] using hvar
                            have hleftSmall : sizeOf left < n := by
                              rw [← hsize]
                              decreasing_trivial
                            have hrightSmall : sizeOf right < n := by
                              rw [← hsize]
                              decreasing_trivial
                            rcases hvar' with hvar | hvar
                            · apply ih (sizeOf left) hleftSmall left rfl
                              rw [hleft]
                              simp only [List.flatMap_cons, List.mem_append]
                              exact Or.inl hvar
                            · apply ih (sizeOf right) hrightSmall right rfl
                              rw [hright]
                              simp only [List.flatMap_cons, List.mem_append]
                              exact Or.inl hvar
        | shift operator left right =>
            cases hleft : compileExp context left with
            | mk leftExpressions leftShape =>
                cases hright : compileExp context right with
                | mk rightExpressions rightShape =>
                    cases leftExpressions with
                    | nil => simp [compileExp, hleft, hright]
                    | cons leftHead leftTail =>
                        cases rightExpressions with
                        | nil => simp [compileExp, hleft, hright]
                        | cons rightHead rightTail =>
                            intro varName hvar
                            have hvar' : varName ∈ crepExpVars leftHead ∨
                                varName ∈ crepExpVars rightHead := by
                              simpa only [compileExp, hleft, hright,
                                List.flatMap_cons, List.flatMap_nil,
                                List.mem_append, List.not_mem_nil, or_false,
                                crepExpVars,
                                List.mem_append] using hvar
                            have hleftSmall : sizeOf left < n := by
                              rw [← hsize]
                              decreasing_trivial
                            have hrightSmall : sizeOf right < n := by
                              rw [← hsize]
                              decreasing_trivial
                            rcases hvar' with hvar | hvar
                            · apply ih (sizeOf left) hleftSmall left rfl
                              rw [hleft]
                              simp only [List.flatMap_cons, List.mem_append]
                              exact Or.inl hvar
                            · apply ih (sizeOf right) hrightSmall right rfl
                              rw [hright]
                              simp only [List.flatMap_cons, List.mem_append]
                              exact Or.inl hvar
        | baseAddr => simp [compileExp, crepExpVars]
        | topAddr => simp [compileExp, crepExpVars]
        | bytesInWord => simp [compileExp]
  exact hmain (sizeOf expression) expression rfl

end Flapjack
