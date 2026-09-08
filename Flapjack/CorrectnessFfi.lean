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

end Flapjack
