import Flapjack.Correctness

/-!
Source-to-Loop correctness for the compiler's FFI lowering.

The lower-level Loop evaluator already exposes an equation for an `ffi` node,
but the compiler boundary was previously only exercised by concrete tests.
This theorem names the composed equation for a closed `extCall`: compiling the
four constant arguments, lowering the resulting Crepe call, and executing it
with a no-op handler produces the same normal result as the source program.
-/

namespace Flapjack

theorem compilePanToLoop_extCall_const_noop_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (state : LoopState α) (locals : VarName → Option α)
    (function : FunName) (configuration configurationLength array arrayLength : α) :
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ state => some state) 40 state
      (loopCompileProg loopContext []
        (compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength))))).map
        loopResultValues =
      (evalPanProgWithCallsAndFfi []
        (fun _ _ _ _ _ locals => some locals) 20 locals
        (.extCall function (.const configuration)
          (.const configurationLength) (.const array) (.const arrayLength))).map
        (fun result =>
          match result with
          | .normal _ => []
          | .returned _ values => values
          | .raised _ _ _ => []) := by
  have hcompile :
      compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength)) =
        nestedDecs [compileContext.maxVar + 1, compileContext.maxVar + 2,
          compileContext.maxVar + 3, compileContext.maxVar + 4]
          [.const configuration, .const configurationLength,
            .const array, .const arrayLength]
          (.extCall function (compileContext.maxVar + 1)
            (compileContext.maxVar + 2) (compileContext.maxVar + 3)
            (compileContext.maxVar + 4)) := by
    simp [compileProg, firstCompiledExp, compileExp, nestedDecs]
  rw [hcompile]
  simp [nestedDecs, loopCompileProg,
    loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    updateLoopLocal, evalPanProgWithCallsAndFfi, evalPanExtCall,
    evalPanExp, loopResultValues]

/-!
The no-op theorem above is useful for a closed regression, but it hides the
host transition behind one particular handler.  This contract separates the
compiler-generated argument plumbing from the host effect: if both host
interfaces succeed for every incoming state, the compiled and source
programs have the same observable control result.  The resulting states are
deliberately left abstract for the next state-relation theorem.
-/
theorem compilePanToLoop_extCall_const_success_projection
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (state : LoopState α) (locals : VarName → Option α)
    (loopHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sourceHandler : FunName → α → α → α → α →
      (VarName → Option α) → Option (VarName → Option α))
    (function : FunName) (configuration configurationLength array arrayLength : α)
    (loopHandler_succeeds : ∀ handlerState,
      ∃ nextState,
        loopHandler function configuration configurationLength array arrayLength
          handlerState = some nextState)
    (sourceHandler_succeeds : ∀ handlerLocals,
      ∃ nextLocals,
        sourceHandler function configuration configurationLength array arrayLength
          handlerLocals = some nextLocals) :
    (evalLoopProgWithCallsAndFfi [] loopHandler 40 state
      (loopCompileProg loopContext []
        (compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength))))).map
        loopResultValues =
      (evalPanProgWithCallsAndFfi [] sourceHandler 20 locals
        (.extCall function (.const configuration)
          (.const configurationLength) (.const array) (.const arrayLength))).map
        (fun result =>
          match result with
          | .normal _ => []
          | .returned _ values => values
          | .raised _ _ _ => []) := by
  have hloopSome (handlerState : LoopState α) :
      ((loopHandler function configuration configurationLength array arrayLength
        handlerState).bind (fun nextState =>
          some (LoopResult.normal nextState))).map
          loopResultValues = some [] := by
    rcases loopHandler_succeeds handlerState with ⟨nextState, hnextState⟩
    simp [hnextState, loopResultValues]
  have hsourceSome (handlerLocals : VarName → Option α) :
      ((sourceHandler function configuration configurationLength array arrayLength
        handlerLocals).bind (fun nextLocals =>
          some (PanControlResult.normal nextLocals))).map
          (fun result =>
            match result with
            | .normal _ => []
            | .returned _ values => values
            | .raised _ _ _ => []) = some [] := by
    rcases sourceHandler_succeeds handlerLocals with ⟨nextLocals, hnextLocals⟩
    simp [hnextLocals]
  have hcompile :
      compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength)) =
        nestedDecs [compileContext.maxVar + 1, compileContext.maxVar + 2,
          compileContext.maxVar + 3, compileContext.maxVar + 4]
          [.const configuration, .const configurationLength,
            .const array, .const arrayLength]
          (.extCall function (compileContext.maxVar + 1)
            (compileContext.maxVar + 2) (compileContext.maxVar + 3)
            (compileContext.maxVar + 4)) := by
    simp [compileProg, firstCompiledExp, compileExp, nestedDecs]
  rw [hcompile]
  simp [nestedDecs, loopCompileProg,
    loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    updateLoopLocal, evalPanProgWithCallsAndFfi, evalPanExtCall,
    evalPanExp, hloopSome, hsourceSome]

end Flapjack
