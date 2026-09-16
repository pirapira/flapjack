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

theorem evalLoopCompiledExtCall
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α) (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (fuel : Nat) (state : LoopState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configuration' configurationLength' array' arrayLength' : Nat)
    (hconfiguration : lookupNatInfo configuration context.vars = some configuration')
    (hconfigurationLength :
      lookupNatInfo configurationLength context.vars = some configurationLength')
    (harray : lookupNatInfo array context.vars = some array')
    (harrayLength : lookupNatInfo arrayLength context.vars = some arrayLength') :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) =
      (do
        let configuration ← state.locals configuration'
        let configurationLength ← state.locals configurationLength'
        let array ← state.locals array'
        let arrayLength ← state.locals arrayLength'
        let state ← ffiHandler function configuration configurationLength array arrayLength state
        pure (.normal state)) := by
  rw [loopCompileProg_extCall context live function configuration
    configurationLength array arrayLength configuration' configurationLength' array'
    arrayLength' hconfiguration hconfigurationLength harray harrayLength]
  exact evalLoopProgWithCallsAndFfi_ffi functions ffiHandler fuel state function
    configuration' configurationLength' array' arrayLength' live

theorem compilePanToLoop_extCall_const_noop_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (state : LoopState α) (locals : VarName → Option α)
    (function : FunName) (configuration configurationLength array arrayLength : α)
    (maxVar_agrees : loopContext.maxVar =
      maxCrepExpVar [.const configuration, .const configurationLength,
        .const array, .const arrayLength]) :
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
  let base : Nat :=
    maxCrepExpVar [.const configuration, .const configurationLength,
      .const array, .const arrayLength] + 1
  have hcompile :
      compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength)) =
        nestedDecs [base, base + 1, base + 2, base + 3]
          [.const configuration, .const configurationLength,
            .const array, .const arrayLength]
          (.extCall function base (base + 1) (base + 2) (base + 3)) := by
    simp [base, compileProg, firstCompiledExp, compileExp, nestedDecs]
  rw [hcompile]
  simp [nestedDecs, loopCompileProg,
    loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    updateLoopLocal, evalPanProgWithCallsAndFfi, evalPanExtCall,
    evalPanExp, loopResultValues, lookupNatInfo, maxVar_agrees, base]

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
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
          handlerLocals = some nextLocals)
    (maxVar_agrees : loopContext.maxVar =
      maxCrepExpVar [.const configuration, .const configurationLength,
        .const array, .const arrayLength]) :
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
  let base : Nat :=
    maxCrepExpVar [.const configuration, .const configurationLength,
      .const array, .const arrayLength] + 1
  have hcompile :
      compileProg compileContext
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength)) =
        nestedDecs [base, base + 1, base + 2, base + 3]
          [.const configuration, .const configurationLength,
            .const array, .const arrayLength]
          (.extCall function base (base + 1) (base + 2) (base + 3)) := by
    simp [base, compileProg, firstCompiledExp, compileExp, nestedDecs]
  rw [hcompile]
  obtain ⟨nextState, hnextState⟩ := loopHandler_succeeds ({
    locals :=
      updateLoopLocal
        (updateLoopLocal
          (updateLoopLocal (updateLoopLocal state.locals (loopContext.maxVar + 1) configuration)
            (loopContext.maxVar + 1 + 1) configurationLength)
          (loopContext.maxVar + 1 + 1 + 1) array)
        (loopContext.maxVar + 1 + 1 + 1 + 1) arrayLength,
    globals := state.globals, memory := state.memory } : LoopState α)
  have hnextState' := hnextState
  simp [maxVar_agrees] at hnextState'
  simp [nestedDecs, loopCompileProg,
    loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    updateLoopLocal, evalPanProgWithCallsAndFfi, evalPanExtCall,
    evalPanExp, hsourceSome, lookupNatInfo, maxVar_agrees, hnextState',
    loopResultValues, base]

end Flapjack
