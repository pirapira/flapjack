import Flapjack.CrepeDeclarationFuelInversion
import Flapjack.CrepeExpressionStability
import Flapjack.CrepeNestedDecsStability

/-!
Inversion of nested declaration evaluation when all bound names are fresh for
the expression list.  The declaration evaluator sees progressively updated
locals, but expression non-interference lets us recover the original flat
evaluation result at every step.  This is the target-side bridge needed by the
temporary structured-assignment constructor.
-/

namespace Flapjack

theorem crepNestedDecsEval_assignList_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (values : List α)
    (body : CrepProg α) (result : CrepControlResult α)
    (hlength : names.length = expressions.length)
    (hdistinct : CrepDistinctNames names)
    (hfresh : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hnested : CrepNestedDecsEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values }
      body = some result := by
  induction names generalizing expressions values state result with
  | nil =>
      cases expressions with
      | nil =>
          have hvalues : values = [] := by
            simpa [evalCrepFullExps] using heval
          cases hvalues
          simpa [CrepNestedDecsEval, updateCrepLocalList] using hnested
      | cons expression expressions =>
          simp at hlength
  | cons name names ih =>
      rcases hdistinct with ⟨hnameNotTail, htailDistinct⟩
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          have hlengthTail : names.length = expressions.length := by
            simpa using hlength
          rcases hnested with ⟨headValue, hhead, htail⟩
          cases htailEval : evalCrepFullExps state.locals state.memory
                  baseAddress topAddress expressions with
              | none =>
                  simp [evalCrepFullExps, hhead, htailEval] at heval
              | some tailValues =>
                  have hvalues : headValue :: tailValues = values := by
                    simpa [evalCrepFullExps, hhead, htailEval] using heval
                  cases hvalues
                  have htailStable :
                      evalCrepFullExps
                        (updateCrepLocal state.locals name headValue)
                        state.memory baseAddress topAddress expressions =
                        some tailValues := by
                    exact evalCrepFullExps_update_of_forall_not_mem
                      state.locals state.memory baseAddress topAddress expressions
                      name headValue
                      (fun current hcurrent =>
                        hfresh name (by simp) current (by simp [hcurrent]))
                      tailValues htailEval
                  have htailResult := ih
                    (expressions := expressions) (values := tailValues)
                    (state := { state with
                      locals := updateCrepLocal state.locals name headValue })
                    (result := result) hlengthTail htailDistinct
                    (fun current hcurrent expression hexpression =>
                      hfresh current (by simp [hcurrent]) expression
                        (by simp [hexpression]))
                    htailStable htail
                  simpa [updateCrepLocalList] using htailResult

theorem crepNestedDecsStateEval_assignList_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (values : List α)
    (body : CrepProg α) (result : CrepControlResult α)
    (hlength : names.length = expressions.length)
    (hdistinct : CrepDistinctNames names)
    (hfresh : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExpsState state baseAddress topAddress expressions =
      some values)
    (hnested : CrepNestedDecsStateEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values }
      body = some result := by
  induction names generalizing expressions values state result with
  | nil =>
      cases expressions with
      | nil =>
          have hvalues : values = [] := by
            simpa [evalCrepFullExpsState] using heval
          cases hvalues
          simpa [CrepNestedDecsStateEval, updateCrepLocalList] using hnested
      | cons expression expressions => simp at hlength
  | cons name names ih =>
      rcases hdistinct with ⟨hnameNotTail, htailDistinct⟩
      cases expressions with
      | nil => simp at hlength
      | cons expression expressions =>
          have hlengthTail : names.length = expressions.length := by
            simpa using hlength
          rcases hnested with ⟨headValue, hhead, htail⟩
          cases htailEval : evalCrepFullExpsState state baseAddress topAddress
              expressions with
          | none => simp [evalCrepFullExpsState, hhead, htailEval] at heval
          | some tailValues =>
              have hvalues : headValue :: tailValues = values := by
                simpa [evalCrepFullExpsState, hhead, htailEval] using heval
              cases hvalues
              have htailStable :
                  evalCrepFullExpsState
                    { state with locals := updateCrepLocal state.locals name headValue }
                    baseAddress topAddress expressions = some tailValues := by
                exact evalCrepFullExpsState_update_of_forall_not_mem
                  state baseAddress topAddress expressions name headValue
                  (fun current hcurrent =>
                    hfresh name (by simp) current (by simp [hcurrent]))
                  tailValues htailEval
              have htailResult := ih
                (expressions := expressions) (values := tailValues)
                (state := { state with
                  locals := updateCrepLocal state.locals name headValue })
                (result := result) hlengthTail htailDistinct
                (fun current hcurrent expression hexpression =>
                  hfresh current (by simp [hcurrent]) expression
                    (by simp [hexpression]))
                htailStable htail
              simpa [updateCrepLocalList] using htailResult

end Flapjack
