import Flapjack.CrepeExpressionStability
import Flapjack.CrepeNestedDecsStability

/-!
Evaluation of the assignment sequence used by `compileProg` for a flattened
local assignment.  The expressions are evaluated in the incoming locals and
then installed in order; the non-interference premise is exactly what makes
that sequential evaluation agree with `evalCrepFullExps`.
-/

namespace Flapjack

theorem evalCrepFullProg_assignList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (slots : List Nat) (expressions : List (CrepExp α)) (values : List α)
    (hlength : slots.length = expressions.length)
    (hdistinct : CrepDistinctNames slots)
    (hnot : ∀ slot ∈ slots, ∀ expression ∈ expressions,
      slot ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + slots.length + 1) state
      (crepNestedSeq (slots.zipWith
        (fun name expression => .assign name expression) expressions)) =
      some (.normal { state with
        locals := updateCrepLocalList state.locals slots values }) := by
  induction slots generalizing expressions values state with
  | nil =>
      cases expressions with
      | nil =>
          cases values with
          | nil =>
              simpa [crepNestedSeq, updateCrepLocalList] using
                (show evalCrepFullProg functions primitive ffi sharedMem
                  baseAddress topAddress (fuel + 1) state .skip =
                    some (.normal state) by
                  simp [evalCrepFullProg])
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
                      have htailResult := ih
                        (state := { state with
                          locals := updateCrepLocal state.locals slot value })
                        (expressions := expressions) (values := values)
                        hlengthTail htailDistinct
                        (fun current hcurrent expression' hexpression' =>
                          hnot current (by simp [hcurrent]) expression'
                            (by simp [hexpression']))
                        htailStable
                      change evalCrepFullProg functions primitive ffi sharedMem
                        baseAddress topAddress
                        ((fuel + slots.length + 1) + 1) state
                        (.seq (.assign slot expression)
                          (crepNestedSeq (List.zipWith
                            (fun name expression => .assign name expression)
                            slots expressions))) = _
                      simp [evalCrepFullProg, hhead]
                      rw [htailResult]
                      rfl

end Flapjack
