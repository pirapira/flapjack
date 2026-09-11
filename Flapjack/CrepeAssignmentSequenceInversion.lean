import Flapjack.CrepeAssignmentSequenceCorrectness

/-!
Converse of the flattened assignment-sequence evaluator equation.  The
program correctness predicate receives a successful target evaluation at an
arbitrary fuel amount, so it needs this inversion rather than only the
forward, sufficiently-fueled equation.
-/

namespace Flapjack

theorem evalCrepFullProg_assignList_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat) (state : CrepState α)
    (slots : List Nat) (expressions : List (CrepExp α)) (values : List α)
    (result : CrepControlResult α)
    (hlength : slots.length = expressions.length)
    (hdistinct : CrepDistinctNames slots)
    (hnot : ∀ slot ∈ slots, ∀ expression ∈ expressions,
      slot ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hresult : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (crepNestedSeq (slots.zipWith
        (fun name expression => .assign name expression) expressions)) =
      some result) :
    result = .normal { state with
      locals := updateCrepLocalList state.locals slots values } := by
  induction slots generalizing expressions values targetFuel state result with
  | nil =>
      cases expressions with
      | nil =>
          cases values with
          | nil =>
              cases targetFuel with
              | zero => simp [crepNestedSeq, evalCrepFullProg] at hresult
              | succ targetFuel =>
                  simpa [crepNestedSeq, evalCrepFullProg,
                    updateCrepLocalList] using hresult.symm
          | cons value values =>
              simp [evalCrepFullExps] at heval
      | cons expression expressions =>
          simp at hlength
  | cons slot slots ih =>
      rcases hdistinct with ⟨hslotNotTail, htailDistinct⟩
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          cases values with
          | nil =>
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none =>
                  simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none =>
                      simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      simp [evalCrepFullExps, hhead, htail] at heval
          | cons value values =>
              have hlengthTail : slots.length = expressions.length := by
                simp only [List.length_cons] at hlength
                omega
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none =>
                  simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none =>
                      simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      have hvalues : headValue :: tailValues = value :: values := by
                        simpa [evalCrepFullExps, hhead, htail] using heval
                      cases hvalues
                      have htailStable :
                          evalCrepFullExps
                            (updateCrepLocal state.locals slot value)
                            state.memory baseAddress topAddress expressions =
                            some values := by
                        exact evalCrepFullExps_update_of_forall_not_mem
                          state.locals state.memory baseAddress topAddress
                          expressions slot value
                          (fun current hcurrent =>
                            hnot slot (by simp) current (by simp [hcurrent]))
                          values htail
                      cases targetFuel with
                      | zero =>
                          simp [crepNestedSeq, evalCrepFullProg] at hresult
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              simp [crepNestedSeq, evalCrepFullProg] at hresult
                          | succ targetFuel =>
                              cases htailResult : evalCrepFullProg
                                  functions primitive ffi sharedMem
                                  baseAddress topAddress (targetFuel + 1)
                                  { state with
                                    locals := updateCrepLocal state.locals slot value }
                                  (crepNestedSeq (List.zipWith
                                    (fun name expression =>
                                      .assign name expression) slots expressions)) with
                              | none =>
                                  simp [crepNestedSeq, evalCrepFullProg, hhead,
                                    htailResult] at hresult
                              | some tailResult =>
                                  have htailEq : tailResult = result := by
                                    simpa [crepNestedSeq, evalCrepFullProg,
                                      hhead, htailResult] using hresult
                                  have htailNot :
                                      ∀ current ∈ slots,
                                        ∀ currentExpression ∈ expressions,
                                          current ∉ crepExpVars currentExpression := by
                                    intro current hcurrent currentExpression hcurrentExpression
                                    exact hnot current (by simp [hcurrent])
                                      currentExpression (by simp [hcurrentExpression])
                                  have htailInv := ih
                                    (expressions := expressions) (values := values)
                                    (targetFuel := targetFuel + 1)
                                    (state := { state with
                                      locals := updateCrepLocal state.locals slot value })
                                    (result := tailResult)
                                    hlengthTail htailDistinct htailNot
                                    htailStable htailResult
                                  cases htailEq
                                  exact htailInv

end Flapjack
