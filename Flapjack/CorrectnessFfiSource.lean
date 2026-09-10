import Flapjack.CrepToLoopCorrectness

namespace Flapjack

/-! The source-local FFI boundary is kept explicit for future pass proofs. -/

def sourceFfiSetupState (state : LoopState α) (base : Nat)
    (configuration configurationLength array arrayLength : α) : LoopState α :=
  { state with locals := (updateLoopLocal
      (updateLoopLocal
        (updateLoopLocal
            (updateLoopLocal state.locals (base + 1) configuration)
            (base + 2) configurationLength)
          (base + 3) array)
      (base + 4) arrayLength) }

theorem compilePanToLoop_extCall_local_state_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (state : LoopState α) (sourceLocals : VarName → Option α)
    (loopHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sourceHandler : PanFfiHandler α) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (nextState : LoopState α) (nextLocals : VarName → Option α)
    (relation : LoopState α → (VarName → Option α) → Prop)
    (hmaxVar : compileContext.maxVar = loopContext.maxVar)
    (hconfigurationVar : lookupInfo "configuration" compileContext.vars =
      some (.one, [compileContext.maxVar + 1]))
    (hconfigurationLengthVar : lookupInfo "configurationLength" compileContext.vars =
      some (.one, [compileContext.maxVar + 2]))
    (harrayVar : lookupInfo "array" compileContext.vars =
      some (.one, [compileContext.maxVar + 3]))
    (harrayLengthVar : lookupInfo "arrayLength" compileContext.vars =
      some (.one, [compileContext.maxVar + 4]))
    (hconfiguration : sourceLocals "configuration" = some configuration)
    (hconfigurationLength : sourceLocals "configurationLength" = some configurationLength)
    (harray : sourceLocals "array" = some array)
    (harrayLength : sourceLocals "arrayLength" = some arrayLength)
    (hslotConfiguration : state.locals (compileContext.maxVar + 1) = sourceLocals "configuration")
    (hslotConfigurationLength : state.locals (compileContext.maxVar + 2) = sourceLocals "configurationLength")
    (hslotArray : state.locals (compileContext.maxVar + 3) = sourceLocals "array")
    (hslotArrayLength : state.locals (compileContext.maxVar + 4) = sourceLocals "arrayLength")
    (hhandler : loopHandler function configuration configurationLength array arrayLength
      (sourceFfiSetupState state compileContext.maxVar configuration configurationLength
        array arrayLength) = some nextState)
    (hsource : evalPanExtCall sourceHandler sourceLocals function
      (.var .local "configuration") (.var .local "configurationLength")
      (.var .local "array") (.var .local "arrayLength") = some nextLocals)
    (hrelation : relation nextState nextLocals) :
    evalLoopProgWithCallsAndFfi [] loopHandler 40 state
      (loopCompileProg loopContext []
        (compileProg compileContext
          (.extCall function (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")))) = some (.normal nextState) ∧
    evalPanProgWithCallsAndFfi [] sourceHandler 20 sourceLocals
      (.extCall function (.var .local "configuration")
        (.var .local "configurationLength") (.var .local "array")
        (.var .local "arrayLength")) = some (.normal nextLocals) ∧
    relation nextState nextLocals := by
  have hcompile :
      compileProg compileContext
          (.extCall function (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")) =
        nestedDecs [compileContext.maxVar + 1, compileContext.maxVar + 2,
          compileContext.maxVar + 3, compileContext.maxVar + 4]
          [.var (compileContext.maxVar + 1), .var (compileContext.maxVar + 2),
            .var (compileContext.maxVar + 3), .var (compileContext.maxVar + 4)]
          (.extCall function (compileContext.maxVar + 1)
            (compileContext.maxVar + 2) (compileContext.maxVar + 3)
            (compileContext.maxVar + 4)) := by
    simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
      hconfigurationVar, hconfigurationLengthVar, harrayVar, harrayLengthVar]
  have hloop :
      evalLoopProgWithCallsAndFfi [] loopHandler 40 state
        (loopCompileProg loopContext []
          (nestedDecs [compileContext.maxVar + 1, compileContext.maxVar + 2,
            compileContext.maxVar + 3, compileContext.maxVar + 4]
            [.var (compileContext.maxVar + 1), .var (compileContext.maxVar + 2),
              .var (compileContext.maxVar + 3), .var (compileContext.maxVar + 4)]
            (.extCall function (compileContext.maxVar + 1)
              (compileContext.maxVar + 2) (compileContext.maxVar + 3)
              (compileContext.maxVar + 4)))) = some (.normal nextState) := by
    have hslotConfiguration' : state.locals (loopContext.maxVar + 1) = some configuration := by
      rw [← hmaxVar, hslotConfiguration, hconfiguration]
    have hslotConfigurationLength' : state.locals (loopContext.maxVar + 2) =
        some configurationLength := by
      rw [← hmaxVar, hslotConfigurationLength, hconfigurationLength]
    have hslotArray' : state.locals (loopContext.maxVar + 3) = some array := by
      rw [← hmaxVar, hslotArray, harray]
    have hslotArrayLength' : state.locals (loopContext.maxVar + 4) =
        some arrayLength := by
      rw [← hmaxVar, hslotArrayLength, harrayLength]
    have hhandler' : loopHandler function configuration configurationLength array arrayLength
        (sourceFfiSetupState state loopContext.maxVar configuration configurationLength
          array arrayLength) = some nextState := by
      rw [← hmaxVar]
      exact hhandler
    have hhandler'' : loopHandler function configuration configurationLength array arrayLength
        { locals :=
            updateLoopLocal
              (updateLoopLocal
                (updateLoopLocal
                  (updateLoopLocal state.locals (loopContext.maxVar + 1) configuration)
                  (loopContext.maxVar + 2) configurationLength)
                (loopContext.maxVar + 3) array)
              (loopContext.maxVar + 4) arrayLength,
          globals := state.globals, memory := state.memory } = some nextState := by
      simpa [sourceFfiSetupState] using hhandler'
    rw [hmaxVar]
    simp [nestedDecs, loopCompileProg, loopCompileExp,
      loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      updateLoopLocal, hslotConfiguration', hslotConfigurationLength',
      hslotArray', hslotArrayLength', hhandler'']
  have hsourceResult :
    evalPanProgWithCallsAndFfi [] sourceHandler 20 sourceLocals
        (.extCall function (.var .local "configuration")
        (.var .local "configurationLength") (.var .local "array")
          (.var .local "arrayLength")) = some (.normal nextLocals) := by
    have hsource' : sourceHandler function configuration configurationLength array arrayLength
        sourceLocals = some nextLocals := by
      simpa [evalPanExtCall, evalPanExp, hconfiguration, hconfigurationLength,
        harray, harrayLength] using hsource
    simp [evalPanProgWithCallsAndFfi, evalPanExtCall, evalPanExp,
      hconfiguration, hconfigurationLength, harray, harrayLength, hsource']
  exact ⟨by rw [hcompile]; exact hloop, hsourceResult, hrelation⟩

/-! Once an FFI leaf has established the state relation, ordinary sequencing
    can thread an arbitrary continuation through both evaluators.  Keeping the
    compiled continuation as an explicit argument makes this theorem useful
    before the complete pass-level relation is assembled. -/

theorem compilePanToLoop_seq_after_extCall
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (state : LoopState α) (sourceLocals : VarName → Option α)
    (loopHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sourceHandler : PanFfiHandler α) (function : FunName)
    (nextState : LoopState α) (nextLocals : VarName → Option α)
    (second : Prog α) (compiledSecond : LoopProg α)
    (sourceResult : PanControlResult α) (loopResult : LoopResult α)
    (hfirstLoop :
      evalLoopProgWithCallsAndFfi [] loopHandler 40 state
        (loopCompileProg loopContext []
          (compileProg compileContext
            (.extCall function (.var .local "configuration")
              (.var .local "configurationLength") (.var .local "array")
              (.var .local "arrayLength")))) = some (.normal nextState))
    (hfirstSource :
      evalPanProgWithCallsAndFfi [] sourceHandler 20 sourceLocals
        (.extCall function (.var .local "configuration")
          (.var .local "configurationLength") (.var .local "array")
          (.var .local "arrayLength")) = some (.normal nextLocals))
    (hcompiledSecond : loopCompileProg loopContext []
      (compileProg compileContext second) = compiledSecond)
    (hloopSecond : evalLoopProgWithCallsAndFfi [] loopHandler 40 nextState
      compiledSecond = some loopResult)
    (hsourceSecond : evalPanProgWithCallsAndFfi [] sourceHandler 20 nextLocals
      second = some sourceResult) :
    evalLoopProgWithCallsAndFfi [] loopHandler 41 state
      (loopCompileProg loopContext []
        (compileProg compileContext
          (.seq (.extCall function (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")) second))) = some loopResult ∧
    evalPanProgWithCallsAndFfi [] sourceHandler 21 sourceLocals
      (.seq (.extCall function (.var .local "configuration")
        (.var .local "configurationLength") (.var .local "array")
        (.var .local "arrayLength")) second) = some sourceResult := by
  constructor
  · have hcompiledSeq :
        loopCompileProg loopContext []
            (compileProg compileContext
              (.seq (.extCall function (.var .local "configuration")
                (.var .local "configurationLength") (.var .local "array")
                (.var .local "arrayLength")) second)) =
          .seq
            (loopCompileProg loopContext []
              (compileProg compileContext
                (.extCall function (.var .local "configuration")
                  (.var .local "configurationLength") (.var .local "array")
                  (.var .local "arrayLength"))))
            compiledSecond := by
      rw [compileProg_seq, loopCompileProg_seq, hcompiledSecond]
    rw [hcompiledSeq]
    simp [evalLoopProgWithCallsAndFfi, hfirstLoop, hloopSecond]
  · simp [evalPanProgWithCallsAndFfi, hfirstSource, hsourceSecond]

end Flapjack
