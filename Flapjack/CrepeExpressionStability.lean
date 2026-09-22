import Flapjack.CrepeSemantics

/-!
Expression non-interference for fresh Crep locals.  This is the evaluator
lemma needed to discharge temporary-expression stability obligations in
sequential declaration and ExtCall lowering.
-/

namespace Flapjack

theorem evalCrepFullExp_update_of_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) (expression : CrepExp α)
    (temporary : Nat) (value updateValue : α)
    (hnot : temporary ∉ crepExpVars expression)
    (heval : evalCrepFullExp locals memory baseAddress topAddress expression =
      some value) :
    evalCrepFullExp (updateCrepLocal locals temporary updateValue) memory
      baseAddress topAddress expression = some value := by
  let rec go (expression : CrepExp α) (value : α)
      (hnot : temporary ∉ crepExpVars expression)
      (heval : evalCrepFullExp locals memory baseAddress topAddress expression =
        some value) :
      evalCrepFullExp (updateCrepLocal locals temporary updateValue) memory
        baseAddress topAddress expression = some value :=
    match expression with
    | .const constant => by simpa [evalCrepFullExp] using heval
    | .var name => by
        have hne : name ≠ temporary := by
          intro heq
          apply hnot
          simp [crepExpVars, heq]
        simpa [evalCrepFullExp, updateCrepLocal, hne] using heval
    | .load address => by
        cases haddress : evalCrepFullExp locals memory baseAddress topAddress address with
        | none => simp [evalCrepFullExp, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExp, haddress, haddress'] using heval
    | .load32 address => by
        cases haddress : evalCrepFullExp locals memory baseAddress topAddress address with
        | none => simp [evalCrepFullExp, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExp, haddress, haddress'] using heval
    | .loadByte address => by
        cases haddress : evalCrepFullExp locals memory baseAddress topAddress address with
        | none => simp [evalCrepFullExp, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExp, haddress, haddress'] using heval
    | .loadGlob address => by simpa [evalCrepFullExp] using heval
    | .op operator expressions => by
        cases expressions with
        | nil => simp [evalCrepFullExp] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExp] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hnotLeft : temporary ∉ crepExpVars left := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    have hnotRight : temporary ∉ crepExpVars right := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    cases hleft : evalCrepFullExp locals memory baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExp, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExp locals memory baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExp, hleft, hright] at heval
                        | some rightValue =>
                            have hleft' := go left leftValue hnotLeft hleft
                            have hright' := go right rightValue hnotRight hright
                            simpa [evalCrepFullExp, hleft, hright, hleft', hright'] using heval
                | cons expression expressions => simp [evalCrepFullExp] at heval
    | .crepOp operator expressions => by
        cases operator
        cases expressions with
        | nil => simp [evalCrepFullExp] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExp] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hnotLeft : temporary ∉ crepExpVars left := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    have hnotRight : temporary ∉ crepExpVars right := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    cases hleft : evalCrepFullExp locals memory baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExp, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExp locals memory baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExp, hleft, hright] at heval
                        | some rightValue =>
                            have hleft' := go left leftValue hnotLeft hleft
                            have hright' := go right rightValue hnotRight hright
                            simpa [evalCrepFullExp, hleft, hright, hleft', hright'] using heval
                | cons expression expressions => simp [evalCrepFullExp] at heval
    | .cmp operator left right => by
        have hnotLeft : temporary ∉ crepExpVars left := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        have hnotRight : temporary ∉ crepExpVars right := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        cases hleft : evalCrepFullExp locals memory baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExp, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExp locals memory baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExp, hleft, hright] at heval
            | some rightValue =>
                have hleft' := go left leftValue hnotLeft hleft
                have hright' := go right rightValue hnotRight hright
                simpa [evalCrepFullExp, hleft, hright, hleft', hright'] using heval
    | .shift operator left right => by
        have hnotLeft : temporary ∉ crepExpVars left := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        have hnotRight : temporary ∉ crepExpVars right := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        cases hleft : evalCrepFullExp locals memory baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExp, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExp locals memory baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExp, hleft, hright] at heval
            | some rightValue =>
                have hleft' := go left leftValue hnotLeft hleft
                have hright' := go right rightValue hnotRight hright
                simpa [evalCrepFullExp, hleft, hright, hleft', hright'] using heval
    | .baseAddr => by simpa [evalCrepFullExp] using heval
    | .topAddr => by simpa [evalCrepFullExp] using heval
    termination_by structural expression
  exact go expression value hnot heval


theorem evalCrepFullExpState_update_of_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α)
    (baseAddress topAddress : α) (expression : CrepExp α)
    (temporary : Nat) (value updateValue : α)
    (hnot : temporary ∉ crepExpVars expression)
    (heval : evalCrepFullExpState state baseAddress topAddress expression =
      some value) :
    evalCrepFullExpState { state with locals := updateCrepLocal state.locals temporary updateValue }
      baseAddress topAddress expression = some value := by
  let rec go (expression : CrepExp α) (value : α)
      (hnot : temporary ∉ crepExpVars expression)
      (heval : evalCrepFullExpState state baseAddress topAddress expression =
        some value) :
      evalCrepFullExpState { state with locals := updateCrepLocal state.locals temporary updateValue }
        baseAddress topAddress expression = some value :=
    match expression with
    | .const constant => by simpa [evalCrepFullExpState] using heval
    | .var name => by
        have hne : name ≠ temporary := by
          intro heq
          apply hnot
          simp [crepExpVars, heq]
        simpa [evalCrepFullExpState, updateCrepLocal, hne] using heval
    | .load address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExpState, haddress, haddress'] using heval
    | .load32 address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExpState, haddress, haddress'] using heval
    | .loadByte address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            have haddress' := go address addressValue
              (by simpa [crepExpVars] using hnot) haddress
            simpa [evalCrepFullExpState, haddress, haddress'] using heval
    | .loadGlob address => by simpa [evalCrepFullExpState] using heval
    | .op operator expressions => by
        cases expressions with
        | nil => simp [evalCrepFullExpState] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExpState] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hnotLeft : temporary ∉ crepExpVars left := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    have hnotRight : temporary ∉ crepExpVars right := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    cases hleft : evalCrepFullExpState state baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExpState, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExpState state baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExpState, hleft, hright] at heval
                        | some rightValue =>
                            have hleft' := go left leftValue hnotLeft hleft
                            have hright' := go right rightValue hnotRight hright
                            simpa [evalCrepFullExpState, hleft, hright, hleft', hright'] using heval
                | cons expression expressions => simp [evalCrepFullExpState] at heval
    | .crepOp operator expressions => by
        cases operator
        cases expressions with
        | nil => simp [evalCrepFullExpState] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExpState] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hnotLeft : temporary ∉ crepExpVars left := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    have hnotRight : temporary ∉ crepExpVars right := by
                      intro hmem
                      apply hnot
                      simp [crepExpVars, crepExpVars.crepExpVarsList, hmem]
                    cases hleft : evalCrepFullExpState state baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExpState, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExpState state baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExpState, hleft, hright] at heval
                        | some rightValue =>
                            have hleft' := go left leftValue hnotLeft hleft
                            have hright' := go right rightValue hnotRight hright
                            simpa [evalCrepFullExpState, hleft, hright, hleft', hright'] using heval
                | cons expression expressions => simp [evalCrepFullExpState] at heval
    | .cmp operator left right => by
        have hnotLeft : temporary ∉ crepExpVars left := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        have hnotRight : temporary ∉ crepExpVars right := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        cases hleft : evalCrepFullExpState state baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExpState, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExpState state baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExpState, hleft, hright] at heval
            | some rightValue =>
                have hleft' := go left leftValue hnotLeft hleft
                have hright' := go right rightValue hnotRight hright
                simpa [evalCrepFullExpState, hleft, hright, hleft', hright'] using heval
    | .shift operator left right => by
        have hnotLeft : temporary ∉ crepExpVars left := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        have hnotRight : temporary ∉ crepExpVars right := by
          intro hmem
          apply hnot
          simp [crepExpVars, hmem]
        cases hleft : evalCrepFullExpState state baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExpState, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExpState state baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExpState, hleft, hright] at heval
            | some rightValue =>
                have hleft' := go left leftValue hnotLeft hleft
                have hright' := go right rightValue hnotRight hright
                simpa [evalCrepFullExpState, hleft, hright, hleft', hright'] using heval
    | .baseAddr => by simpa [evalCrepFullExpState] using heval
    | .topAddr => by simpa [evalCrepFullExpState] using heval
    termination_by structural expression
  exact go expression value hnot heval


theorem evalCrepFullExps_update_of_forall_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) (expressions : List (CrepExp α))
    (temporary : Nat)
    (updateValue : α)
    (hnot : ∀ expression ∈ expressions,
      temporary ∉ crepExpVars expression)
    (values : List α)
    (heval : evalCrepFullExps locals memory baseAddress topAddress expressions =
      some values) :
    evalCrepFullExps (updateCrepLocal locals temporary updateValue) memory
      baseAddress topAddress expressions = some values := by
  induction expressions generalizing values with
  | nil =>
      simpa [evalCrepFullExps] using heval
  | cons expression expressions ih =>
      have hnotExpression : temporary ∉ crepExpVars expression := by
        exact hnot expression (by simp)
      have hnotExpressions : ∀ expression ∈ expressions,
          temporary ∉ crepExpVars expression := by
        intro expression hmem
        exact hnot expression (by simp [hmem])
      cases hvalue : evalCrepFullExp locals memory baseAddress topAddress expression with
      | none =>
          simp [evalCrepFullExps, hvalue] at heval
      | some value =>
          have hvalue' := evalCrepFullExp_update_of_not_mem
            locals memory baseAddress topAddress expression temporary value updateValue
            hnotExpression hvalue
          cases htail : evalCrepFullExps locals memory baseAddress topAddress expressions with
          | none =>
              simp [evalCrepFullExps, hvalue, htail] at heval
          | some tailValues =>
              have htail' := ih hnotExpressions tailValues htail
              have hvalues : value :: tailValues = values := by
                simpa [evalCrepFullExps, hvalue, htail] using heval
              cases hvalues
              simp [evalCrepFullExps, hvalue', htail']


theorem evalCrepFullExpsState_update_of_forall_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α)
    (baseAddress topAddress : α) (expressions : List (CrepExp α))
    (temporary : Nat)
    (updateValue : α)
    (hnot : ∀ expression ∈ expressions,
      temporary ∉ crepExpVars expression)
    (values : List α)
    (heval : evalCrepFullExpsState state baseAddress topAddress expressions =
      some values) :
    evalCrepFullExpsState { state with locals := updateCrepLocal state.locals temporary updateValue }
      baseAddress topAddress expressions = some values := by
  induction expressions generalizing values with
  | nil =>
      simpa [evalCrepFullExpsState] using heval
  | cons expression expressions ih =>
      have hnotExpression : temporary ∉ crepExpVars expression := by
        exact hnot expression (by simp)
      have hnotExpressions : ∀ expression ∈ expressions,
          temporary ∉ crepExpVars expression := by
        intro expression hmem
        exact hnot expression (by simp [hmem])
      cases hvalue : evalCrepFullExpState state baseAddress topAddress expression with
      | none =>
          simp [evalCrepFullExpsState, hvalue] at heval
      | some value =>
          have hvalue' := evalCrepFullExpState_update_of_not_mem
            state baseAddress topAddress expression temporary value updateValue
            hnotExpression hvalue
          cases htail : evalCrepFullExpsState state baseAddress topAddress expressions with
          | none =>
              simp [evalCrepFullExpsState, hvalue, htail] at heval
          | some tailValues =>
              have htail' := ih hnotExpressions tailValues htail
              have hvalues : value :: tailValues = values := by
                simpa [evalCrepFullExpsState, hvalue, htail] using heval
              cases hvalues
              simp [evalCrepFullExpsState, hvalue', htail']

/-- Cake's `eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:835`):
a successfully evaluated expression binds every variable that occurs in it. -/
theorem evalCrepFullExpState_local_lookup_of_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expression : CrepExp α) (value : α) (name : Nat)
    (heval : evalCrepFullExpState state baseAddress topAddress expression = some value)
    (hmem : name ∈ crepExpVars expression) :
    ∃ w, state.locals name = some w := by
  let rec go (expression : CrepExp α) (value : α)
      (heval : evalCrepFullExpState state baseAddress topAddress expression = some value)
      (hmem : name ∈ crepExpVars expression) :
      ∃ w, state.locals name = some w :=
    match expression with
    | .const _ => by simp at hmem
    | .var variableName => by
        have hname : name = variableName := by simpa [crepExpVars] using hmem
        exact ⟨value, by rw [hname]; simpa [evalCrepFullExpState] using heval⟩
    | .load address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            exact go address addressValue haddress (by simpa [crepExpVars] using hmem)
    | .load32 address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            exact go address addressValue haddress (by simpa [crepExpVars] using hmem)
    | .loadByte address => by
        cases haddress : evalCrepFullExpState state baseAddress topAddress address with
        | none => simp [evalCrepFullExpState, haddress] at heval
        | some addressValue =>
            exact go address addressValue haddress (by simpa [crepExpVars] using hmem)
    | .loadGlob _ => by simp [crepExpVars] at hmem
    | .op operator expressions => by
        cases expressions with
        | nil => simp [evalCrepFullExpState] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExpState] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hmem' : name ∈ crepExpVars left ∨ name ∈ crepExpVars right := by
                      simpa [crepExpVars, crepExpVars.crepExpVarsList] using hmem
                    cases hleft : evalCrepFullExpState state baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExpState, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExpState state baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExpState, hleft, hright] at heval
                        | some rightValue =>
                            rcases hmem' with hmemLeft | hmemRight
                            · exact go left leftValue hleft hmemLeft
                            · exact go right rightValue hright hmemRight
                | cons expression expressions => simp [evalCrepFullExpState] at heval
    | .crepOp operator expressions => by
        cases operator
        cases expressions with
        | nil => simp [evalCrepFullExpState] at heval
        | cons left expressions =>
            cases expressions with
            | nil => simp [evalCrepFullExpState] at heval
            | cons right expressions =>
                cases expressions with
                | nil =>
                    have hmem' : name ∈ crepExpVars left ∨ name ∈ crepExpVars right := by
                      simpa [crepExpVars, crepExpVars.crepExpVarsList] using hmem
                    cases hleft : evalCrepFullExpState state baseAddress topAddress left with
                    | none =>
                        simp [evalCrepFullExpState, hleft] at heval
                    | some leftValue =>
                        cases hright : evalCrepFullExpState state baseAddress topAddress right with
                        | none =>
                            simp [evalCrepFullExpState, hleft, hright] at heval
                        | some rightValue =>
                            rcases hmem' with hmemLeft | hmemRight
                            · exact go left leftValue hleft hmemLeft
                            · exact go right rightValue hright hmemRight
                | cons expression expressions => simp [evalCrepFullExpState] at heval
    | .cmp operator left right => by
        have hmem' : name ∈ crepExpVars left ∨ name ∈ crepExpVars right := by
          simpa [crepExpVars] using hmem
        cases hleft : evalCrepFullExpState state baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExpState, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExpState state baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExpState, hleft, hright] at heval
            | some rightValue =>
                rcases hmem' with hmemLeft | hmemRight
                · exact go left leftValue hleft hmemLeft
                · exact go right rightValue hright hmemRight
    | .shift operator left right => by
        have hmem' : name ∈ crepExpVars left ∨ name ∈ crepExpVars right := by
          simpa [crepExpVars] using hmem
        cases hleft : evalCrepFullExpState state baseAddress topAddress left with
        | none =>
            simp [evalCrepFullExpState, hleft] at heval
        | some leftValue =>
            cases hright : evalCrepFullExpState state baseAddress topAddress right with
            | none =>
                simp [evalCrepFullExpState, hleft, hright] at heval
            | some rightValue =>
                rcases hmem' with hmemLeft | hmemRight
                · exact go left leftValue hleft hmemLeft
                · exact go right rightValue hright hmemRight
    | .baseAddr => by simp [crepExpVars] at hmem
    | .topAddr => by simp [crepExpVars] at hmem
    termination_by structural expression
  exact go expression value heval hmem

/-- Helper: a member of the flattened variable lists of a successfully mapped list
comes from an element whose evaluation succeeds. -/
theorem exists_mapM_of_mem_flatten_map {α β γ : Type _}
    (f : α → Option β) (g : α → List γ) (es : List α) (vs : List β) (n : γ)
    (heval : es.mapM f = some vs)
    (hmem : n ∈ (es.map g).flatten) :
    ∃ e ∈ es, ∃ v, f e = some v ∧ n ∈ g e := by
  induction es generalizing vs with
  | nil => simp at hmem
  | cons e es ih =>
      rw [List.mapM_cons] at heval
      cases hfe : f e with
      | none => simp [hfe] at heval
      | some v =>
          simp only [hfe] at heval
          cases hes : es.mapM f with
          | none => simp [hes] at heval
          | some vs' =>
              simp only [hes] at heval
              have hvs : v :: vs' = vs := by simpa using heval
              subst hvs
              simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨e, by simp, v, hfe, hmem⟩
              · obtain ⟨e', he'mem, v', hf', hn'⟩ := ih vs' hes hmem
                exact ⟨e', by simp [he'mem], v', hf', hn'⟩

/-- Cake's `opt_mmap_eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:847`):
a successfully evaluated expression list binds every variable occurring in any
of its expressions. -/
theorem evalCrepFullExpsState_local_lookup_of_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expressions : List (CrepExp α)) (values : List α) (name : Nat)
    (heval : expressions.mapM (evalCrepFullExpState state baseAddress topAddress) = some values)
    (hmem : name ∈ (expressions.map crepExpVars).flatten) :
    ∃ w, state.locals name = some w := by
  obtain ⟨expression, _hexpression, value, hvalue, hmemExpression⟩ :=
    exists_mapM_of_mem_flatten_map
      (evalCrepFullExpState state baseAddress topAddress) crepExpVars
      expressions values name heval hmem
  exact evalCrepFullExpState_local_lookup_of_mem state baseAddress topAddress
    expression value name hvalue hmemExpression

end Flapjack

