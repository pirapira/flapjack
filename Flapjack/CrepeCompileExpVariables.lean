import Flapjack.Pancake.PanToCrep.Compile

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

theorem compileExp_vars_present
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α)
    (expression : Exp α) :
    ∀ varName ∈ (compileExp context expression).1.flatMap crepExpVars,
      ∃ name shape names, lookupInfo name context.vars = some (shape, names) ∧
        varName ∈ names := by
  have hmain : ∀ n (expression : Exp α), sizeOf expression = n →
      ∀ varName ∈ (compileExp context expression).1.flatMap crepExpVars,
        ∃ name shape names, lookupInfo name context.vars = some (shape, names) ∧
          varName ∈ names := by
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
              ∃ name shape names, lookupInfo name context.vars = some (shape, names) ∧
                varName ∈ names := by
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
                      exact ⟨name, shape, names, hlookup, hvar'⟩
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


theorem compileExpList_vars_present
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) :
    ∀ (expressions : List (Exp α)) (varName : Nat),
      varName ∈
        (compileExp.compileExpList context expressions).flatMap
          (fun compiled => compiled.1.flatMap crepExpVars) →
      ∃ name shape names, lookupInfo name context.vars = some (shape, names) ∧
        varName ∈ names := by
  intro expressions
  induction expressions with
  | nil => intro varName hvar; simp [compileExp.compileExpList] at hvar
  | cons expression expressions ih =>
      intro varName hvar
      simp only [compileExp.compileExpList, List.flatMap_cons,
        List.mem_append] at hvar
      rcases hvar with hvar | hvar
      · exact compileExp_vars_present context expression varName hvar
      · exact ih varName hvar

/-! The expression-list companions below are the syntactic part of Cake's
    `compile_exp_not_mem_load_glob` (`pan_to_crepProofScript.sml:2013`).
    Flapjack's localized `compileExp` has no global-load expression case: the
    only `loadGlob` nodes are introduced by the explicit global-load prefix.
    We therefore prove the stronger compiler-only statement, independently of
    the source state relation used by the full Cake theorem. -/

theorem flatMap_fst_crepExps_eq
    (compiled : List (List (CrepExp α) × Shape)) :
    (compiled.flatMap Prod.fst).flatMap crepExps =
      compiled.flatMap (fun entry => entry.1.flatMap crepExps) := by
  exact List.flatMap_assoc

theorem flatMap_map_fst_crepExps_eq
    (compiled : List (List (CrepExp α) × Shape)) :
    (compiled.map Prod.fst).flatMap (List.flatMap crepExps) =
      compiled.flatMap (fun entry => entry.1.flatMap crepExps) := by
  rw [List.flatMap_map]

theorem crepExpsList_eq_flatMap
    (expressions : List (CrepExp α)) :
    crepExps.crepExpsList expressions = expressions.flatMap crepExps := by
  induction expressions with
  | nil => simp [crepExps.crepExpsList]
  | cons expression expressions ih =>
      simp [crepExps.crepExpsList, ih]

theorem cexpHeads_crepExps_mem
    (expressions : List (List (CrepExp α))) (heads : List (CrepExp α))
    (hheads : cexpHeads expressions = some heads) (target : α)
    (hmem : CrepExp.loadGlob target ∈ heads.flatMap crepExps) :
    CrepExp.loadGlob target ∈ expressions.flatMap (List.flatMap crepExps) := by
  induction expressions generalizing heads with
  | nil =>
      simp [cexpHeads] at hheads
      subst heads
      simp at hmem
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
              have hmem' : CrepExp.loadGlob target ∈ crepExps head ∨
                  CrepExp.loadGlob target ∈ restHeads.flatMap crepExps := by
                simpa only [List.flatMap_cons, List.mem_append] using hmem
              rcases hmem' with hmem' | hmem'
              · simp only [List.flatMap_cons, List.mem_append]
                exact Or.inl (Or.inl hmem')
              · have htail := ih restHeads hrest hmem'
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr htail

theorem compileField_crepExps_mem
    [OfNat α 0]
    (index : Nat) (shapes : List Shape) (expressions : List (CrepExp α))
    (target : α) (hmem : CrepExp.loadGlob target ∈
      (compileField index shapes expressions).1.flatMap crepExps) :
    CrepExp.loadGlob target ∈ expressions.flatMap crepExps := by
  induction shapes generalizing index expressions with
  | nil =>
      simp [compileField, crepExps] at hmem
  | cons shape shapes ih =>
      cases index with
      | zero =>
          obtain ⟨expression, hexpression, hmem⟩ :=
            List.mem_flatMap.mp hmem
          exact List.mem_flatMap.mpr ⟨expression,
            List.mem_of_mem_take hexpression, hmem⟩
      | succ index =>
          have hmem' : CrepExp.loadGlob target ∈
              (compileField index shapes
                (expressions.drop (Shape.shapeSize shape))).1.flatMap crepExps := by
            simpa [compileField] using hmem
          have hsource := ih index (expressions.drop (Shape.shapeSize shape)) hmem'
          obtain ⟨expression, hexpression, hmem⟩ :=
            List.mem_flatMap.mp hsource
          exact List.mem_flatMap.mpr ⟨expression,
            List.mem_of_mem_drop hexpression, hmem⟩

theorem compileExp_not_mem_loadGlob
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expression : Exp α) (target : α) :
    CrepExp.loadGlob target ∉
      (compileExp context expression).1.flatMap crepExps := by
  have hmain : ∀ n (expression : Exp α), sizeOf expression = n →
      CrepExp.loadGlob target ∉
        (compileExp context expression).1.flatMap crepExps := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro expression hsize
        have hcompileList : ∀ fields : List (Exp α),
            (∀ field ∈ fields, sizeOf field < n) →
            CrepExp.loadGlob target ∉
              (compileExp.compileExpList context fields).flatMap
                (fun entry => entry.1.flatMap crepExps) := by
          intro fields
          induction fields with
          | nil =>
              intro _
              simp [compileExp.compileExpList]
          | cons field fields ihFields =>
              intro hsmall
              have hfield := ih (sizeOf field)
                (hsmall field (by simp)) field rfl
              have htail := ihFields (fun current hcurrent =>
                hsmall current (by simp [hcurrent]))
              simp only [compileExp.compileExpList, List.flatMap_cons,
                List.mem_append, not_or] at hfield htail ⊢
              exact ⟨hfield, htail⟩
        cases expression with
        | const value => simp [compileExp, crepExps]
        | var kind name =>
            cases kind with
            | «local» =>
                cases hlookup : lookupInfo name context.vars with
                | none => simp [compileExp, hlookup, crepExps]
                | some info =>
                    cases info with
                    | mk shape names =>
                        simp [compileExp, hlookup, crepExps]
            | global => simp [compileExp, crepExps]
        | rStruct fields =>
            have hsmall : ∀ field ∈ fields, sizeOf field < n := by
              intro field hfield
              rw [← hsize]
              decreasing_trivial
            have hfields := hcompileList fields hsmall
            simpa only [compileExp, flatMap_fst_crepExps_eq] using hfields
        | rField index value =>
            cases hcompiled : compileExp context value with
            | mk expressions shape =>
                cases shape with
                | one => simp [compileExp, hcompiled, crepExps]
                | named name => simp [compileExp, hcompiled, crepExps]
                | comb shapes =>
                    intro hmem
                    have hsource := compileField_crepExps_mem index shapes
                      expressions target (by
                        simpa [compileExp, hcompiled] using hmem)
                    have hvalue := ih (sizeOf value) (by
                      rw [← hsize]
                      decreasing_trivial) value rfl
                    apply hvalue
                    simpa [hcompiled] using hsource
        | nStruct name fields => simp [compileExp, crepExps]
        | nField name field => simp [compileExp, crepExps]
        | load shape value =>
            cases hcompiled : compileExp context value with
            | mk expressions resultShape =>
                cases expressions with
                | nil => simp [compileExp, hcompiled, crepExps]
                | cons compiledValue rest =>
                    have hvalue := ih (sizeOf value) (by
                      rw [← hsize]
                      decreasing_trivial) value rfl
                    have hhead : CrepExp.loadGlob target ∉ crepExps compiledValue := by
                      intro hmem
                      apply hvalue
                      simp [hcompiled, hmem]
                    have hload := crepExps_loadShape_not_mem_loadGlob
                      (0 : α) context.bytesInWord (Shape.shapeSize shape)
                      compiledValue target hhead
                    simpa [compileExp, hcompiled] using hload
        | load32 value | loadByte value =>
            cases hcompiled : compileExp context value with
            | mk expressions resultShape =>
                cases expressions with
                | nil => simp [compileExp, hcompiled, crepExps]
                | cons compiledValue rest =>
                    have hvalue := ih (sizeOf value) (by
                      rw [← hsize]
                      decreasing_trivial) value rfl
                    have hhead : CrepExp.loadGlob target ∉ crepExps compiledValue := by
                      intro hmem
                      apply hvalue
                      simp [hcompiled, hmem]
                    cases resultShape with
                    | one =>
                        intro hmem
                        apply hhead
                        simpa [compileExp, hcompiled, crepExps] using hmem
                    | comb shapes => simp [compileExp, hcompiled, crepExps]
                    | named name => simp [compileExp, hcompiled, crepExps]
        | op operator expressions | panOp operator expressions =>
            have hsmall : ∀ field ∈ expressions, sizeOf field < n := by
              intro field hfield
              rw [← hsize]
              decreasing_trivial
            have hcompiledList := hcompileList expressions hsmall
            cases hheads : cexpHeads
                ((compileExp.compileExpList context expressions).map Prod.fst) with
            | none => simp [compileExp, hheads, crepExps]
            | some heads =>
                intro hmem
                have hsource : CrepExp.loadGlob target ∈
                    ((compileExp.compileExpList context expressions).map Prod.fst).flatMap
                      (List.flatMap crepExps) := by
                  have hheadsMem : CrepExp.loadGlob target ∈
                      heads.flatMap crepExps := by
                    simpa [compileExp, hheads, crepExps,
                      crepExpsList_eq_flatMap] using hmem
                  exact cexpHeads_crepExps_mem _ heads hheads target hheadsMem
                apply hcompiledList
                simpa [flatMap_map_fst_crepExps_eq] using hsource
        | cmp operator left right | shift operator left right =>
            cases hleft : compileExp context left with
            | mk leftExpressions leftShape =>
                cases hright : compileExp context right with
                | mk rightExpressions rightShape =>
                    cases leftExpressions with
                    | nil => simp [compileExp, hleft, hright, crepExps]
                    | cons leftHead leftTail =>
                        cases rightExpressions with
                        | nil => simp [compileExp, hleft, hright, crepExps]
                        | cons rightHead rightTail =>
                            have hleft' := ih (sizeOf left) (by
                              rw [← hsize]
                              decreasing_trivial) left rfl
                            have hright' := ih (sizeOf right) (by
                              rw [← hsize]
                              decreasing_trivial) right rfl
                            have hleftList : CrepExp.loadGlob target ∉
                                (leftHead :: leftTail).flatMap crepExps := by
                              simpa [hleft] using hleft'
                            have hrightList : CrepExp.loadGlob target ∉
                                (rightHead :: rightTail).flatMap crepExps := by
                              simpa [hright] using hright'
                            have hleftHead : CrepExp.loadGlob target ∉
                                crepExps leftHead := by
                              intro hmem
                              apply hleftList
                              exact List.mem_flatMap.mpr ⟨leftHead, by simp, hmem⟩
                            have hrightHead : CrepExp.loadGlob target ∉
                                crepExps rightHead := by
                              intro hmem
                              apply hrightList
                              exact List.mem_flatMap.mpr ⟨rightHead, by simp, hmem⟩
                            simpa [compileExp, hleft, hright, crepExps] using
                              And.intro hleftHead hrightHead
        | baseAddr => simp [compileExp, crepExps]
        | topAddr => simp [compileExp, crepExps]
        | bytesInWord => simp [compileExp, crepExps]
  exact hmain (sizeOf expression) expression rfl

/-! Compiler-only support for the exact HOL proof below. This variant follows
    the finite-map, HOL-shaped `compileExpHOL` implementation; the earlier
    `compileExp_not_mem_loadGlob` above is about the separate list-backed
    compatibility compiler and is not used as the tagged theorem's proof. -/

theorem compileExpHOL_not_mem_loadGlob
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (expression : Exp α) (target : α) :
    CrepExp.loadGlob target ∉
      (compileExpHOL context expression).1.flatMap crepExps := by
  let listNoGlobal (expressions : List (Exp α)) :=
    ∀ target, CrepExp.loadGlob target ∉
      (compileExpHOL.compileExpListHOL context expressions).flatMap
        (fun entry => entry.1.flatMap crepExps)
  let expNoGlobal (expression : Exp α) :=
    ∀ target, CrepExp.loadGlob target ∉
      (compileExpHOL context expression).1.flatMap crepExps
  apply compileExpHOL.induct (context := context)
    (motive1 := listNoGlobal) (motive2 := expNoGlobal)
  all_goals try simp_all [compileExpHOL, compileExpHOL.compileExpListHOL,
    listNoGlobal, expNoGlobal, crepExps]
  case case2 =>
    intro expression expressions ihExpression ihExpressions target output shape hpair
      compiledOutput hcompiledOutput
    rcases hpair with hhead | htail
    · have hmem : compiledOutput ∈ (compileExpHOL context expression).1 := by
        rw [← hhead]
        exact hcompiledOutput
      exact ihExpression target compiledOutput hmem
    · exact ihExpressions target output shape htail compiledOutput hcompiledOutput
  case case7 =>
    intro expressions ihExpressions target output compiledOutputs shape hpair compiledOutput
      hcompiledOutput
    exact (ihExpressions target compiledOutputs shape hpair output compiledOutput) hcompiledOutput
  case case8 =>
    intro index expression shapes hshape ihExpression target output houtput
    intro hmem
    have hfield : CrepExp.loadGlob target ∈
        (compileField index shapes (compileExpHOL context expression).1).1.flatMap crepExps :=
      List.mem_flatMap.mpr ⟨output, houtput, hmem⟩
    have hinput := compileField_crepExps_mem index shapes
      (compileExpHOL context expression).1 target hfield
    rcases List.mem_flatMap.mp hinput with ⟨source, hsource, hmem⟩
    exact ihExpression target source hsource hmem
  case case12 =>
    intro shape expression head tail outputShape hcompile ihExpression target output houtput
    have hheadNo : CrepExp.loadGlob target ∉ crepExps head :=
      (ihExpression target).1
    have hload := crepExps_loadShape_not_mem_loadGlob
      (0 : α) CrepBytesInWord.bytesInWord (Shape.shapeSize shape) head target hheadNo
    intro hmem
    apply hload
    exact List.mem_flatMap.mpr ⟨output, houtput, hmem⟩
  case case18 =>
    intro operator expressions heads hheads ihExpressions target
    intro hmem
    have hheadsMem : CrepExp.loadGlob target ∈ heads.flatMap crepExps := by
      simpa [crepExpsList_eq_flatMap] using hmem
    have hinputs := cexpHeads_crepExps_mem
      ((compileExpHOL.compileExpListHOL context expressions).map Prod.fst)
      heads hheads target hheadsMem
    rcases List.mem_flatMap.mp hinputs with ⟨outputs, houtputs, hmem⟩
    rcases List.mem_map.mp houtputs with ⟨entry, hentry, rfl⟩
    rcases entry with ⟨outputs, shape⟩
    rcases List.mem_flatMap.mp hmem with ⟨compiledOutput, hcompiledOutput, hmem⟩
    exact ihExpressions target outputs shape hentry compiledOutput hcompiledOutput hmem
  case case20 =>
    intro operator expressions heads hheads ihExpressions target
    intro hmem
    have hheadsMem : CrepExp.loadGlob target ∈ heads.flatMap crepExps := by
      simpa [crepExpsList_eq_flatMap] using hmem
    have hinputs := cexpHeads_crepExps_mem
      ((compileExpHOL.compileExpListHOL context expressions).map Prod.fst)
      heads hheads target hheadsMem
    rcases List.mem_flatMap.mp hinputs with ⟨outputs, houtputs, hmem⟩
    rcases List.mem_map.mp houtputs with ⟨entry, hentry, rfl⟩
    rcases entry with ⟨outputs, shape⟩
    rcases List.mem_flatMap.mp hmem with ⟨compiledOutput, hcompiledOutput, hmem⟩
    exact ihExpressions target outputs shape hentry compiledOutput hcompiledOutput hmem

/-! Cake's `genlist_vmax_distinct_lists_compiled_exps`
    (`pan_to_crepProofScript.sml:3094`): compiler temporaries allocated strictly
    above `maxVar` cannot occur in the variables of compiled source arguments.
    `List.range` is the Lean counterpart of Cake's `GENLIST`. -/
theorem genlist_vmax_distinct_lists_compiled_exps
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (n : Nat) (argexps : List (Exp α))
    (hbound : ∀ name shape names,
      lookupInfo name context.vars = some (shape, names) →
      ∀ varName ∈ names, varName ≤ context.maxVar) :
    ListDisjoint ((List.range n).map (fun i => i + 1 + context.maxVar))
      ((argexps.map (compileExp context)).flatMap
        (fun entry => entry.1.flatMap crepExpVars)) := by
  apply genlist_distinct_max n context.maxVar _
  intro varName hvar
  simp only [List.mem_flatMap] at hvar
  obtain ⟨compiled, hcompiled, hvar⟩ := hvar
  obtain ⟨expression, _, rfl⟩ := List.mem_map.mp hcompiled
  apply compileExp_vars_bounded context hbound expression varName
  obtain ⟨compiledExpression, hcompiledExpression, hvar⟩ := hvar
  exact List.mem_flatMap.mpr ⟨compiledExpression, hcompiledExpression, hvar⟩

end Flapjack
