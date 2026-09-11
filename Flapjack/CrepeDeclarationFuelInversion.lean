import Flapjack.CrepeDeclarationRelation

/-!
Inversion for successful evaluation of compiler-generated declaration lists.

`evalCrepFullProg_nestedDecs_of_eval` gives the forward direction: a
`CrepNestedDecsEval` witness runs `nestedDecs` with one fuel step per bound
slot.  The converse is needed by the compositional program correctness
induction, which starts from an arbitrary successful target evaluation and
must recover the fuel and result of the continuation body.
-/

namespace Flapjack

theorem crepNestedDecsEval_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (body : CrepProg α)
    (result : CrepControlResult α)
    (hdistinct : CrepDistinctNames names)
    (hlength : names.length = expressions.length)
    (heval : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (nestedDecs names expressions body) = some result) :
    ∃ fuel innerResult,
      targetFuel = fuel + names.length ∧
      CrepNestedDecsEval functions primitive ffi sharedMem
        baseAddress topAddress fuel state names expressions body innerResult ∧
      restoreCrepResultList state.locals names innerResult = result := by
  induction names generalizing targetFuel state expressions result with
  | nil =>
      cases expressions with
      | nil =>
          refine ⟨targetFuel, result, ?_, ?_, ?_⟩
          · simp
          · simpa [CrepNestedDecsEval, nestedDecs] using heval
          · simp [restoreCrepResultList]
      | cons expression expressions =>
          simp at hlength
  | cons name names ih =>
      rcases hdistinct with ⟨hnotmem, htailDistinct⟩
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          have hlength' : names.length = expressions.length := by
            simpa using hlength
          cases targetFuel with
          | zero =>
              simp [nestedDecs, evalCrepFullProg] at heval
          | succ targetFuel =>
              cases hvalue : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none =>
                  simp [nestedDecs, evalCrepFullProg, hvalue] at heval
              | some value =>
                  cases hbody : evalCrepFullProg functions primitive ffi sharedMem
                      baseAddress topAddress targetFuel
                      { state with locals := updateCrepLocal state.locals name value }
                      (nestedDecs names expressions body) with
                  | none =>
                      simp [nestedDecs, evalCrepFullProg, hvalue, hbody] at heval
                  | some innerResult =>
                      have hrestore :
                          restoreCrepResult name (state.locals name) innerResult =
                            result := by
                        simpa [nestedDecs, evalCrepFullProg, hvalue, hbody] using heval
                      have htail := ih
                        (targetFuel := targetFuel)
                        (state := { state with
                          locals := updateCrepLocal state.locals name value })
                        (expressions := expressions) (result := innerResult)
                        htailDistinct hlength' hbody
                      rcases htail with
                        ⟨fuel, bodyResult, hfuel, hnested, htailRestore⟩
                      refine ⟨fuel, bodyResult, ?_, ?_, ?_⟩
                      · simp only [List.length]
                        omega
                      · exact ⟨value, hvalue, hnested⟩
                      · have htailRestoreZero :=
                          restoreCrepResultList_update_of_not_mem
                            state.locals name value names bodyResult hnotmem
                        have hrestore' := hrestore
                        rw [← htailRestore] at hrestore'
                        rw [htailRestoreZero] at hrestore'
                        simpa [restoreCrepResultList] using hrestore'

end Flapjack
