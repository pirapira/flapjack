import Flapjack.CrepeProgramRelation
import Flapjack.CrepeProgramSourceWordLoopFuelRelation
import Flapjack.CrepeProgramLoopFuelRelation

/-!
The compositional `while` constructor for the Pancake source-to-Crep
simulation.  The induction follows the source evaluator's fuel: a normal or
continued body result re-enters the loop with one less fuel, while break,
return, and raise are terminal at the current loop level.
-/

namespace Flapjack

def PanValueCrepProgramLoopControlSafe
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory program = some sourceResult →
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context program) = some crepResult →
    match sourceResult, crepResult with
    | .broke _ _ _, .broke _ label => label = 0
    | .continued _ _ _, .continued _ label => label = 0
    | _, _ => True

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_while_source_word_pos
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hbodySafe : PanValueCrepProgramLoopControlSafe body)
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlookup : ∀ (sourceLocals : VarName → Option (PanValue α)) name value,
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrep : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult) :
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  induction sourceFuel generalizing targetFuel sourceLocals sourceGlobals
      sourceMemory state sourceResult crepResult with
  | zero =>
      cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord condition.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueExp, hcondition] at hsource
      | some conditionValue =>
          cases conditionValue with
          | word sourceCondition =>
              obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord hbytesInWord hrel.2.1
                  (fun name value hvalue =>
                    hlookup sourceLocals name value hvalue)
                  condition sourceCondition hcondition
              by_cases hzero : sourceCondition = 0
              · have hzeroResult := compile_full_pan_value_while_source_word_zero_relation_fuel
                  context structs sourceFunctions functions sourceLocals sourceGlobals
                  sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                  baseAddress topAddress bytesInWord 0 targetFuel condition body
                  (compileProg context body) sourceCondition sourceCondition exceptionRel
                  hbytesInWord hrel (hlookup sourceLocals) hcondition rfl hzero rfl
                have hsourceEq :
                    PanValueControlResult.normal sourceLocals sourceGlobals sourceMemory =
                      sourceResult := by
                  exact Option.some.inj (hzeroResult.1.symm.trans hsource)
                have hcrepEq : CrepControlResult.normal state = crepResult := by
                  exact Option.some.inj (hzeroResult.2.1.symm.trans hcrep)
                cases hsourceEq
                cases hcrepEq
                exact hzeroResult.2.2
              · simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  evalPanValueExp, hcondition, hzero] at hsource
          | rStruct fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, hcondition] at hsource
          | nStruct name fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, hcondition] at hsource
  | succ sourceFuel ih =>
      cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord condition.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueExp, hcondition] at hsource
      | some conditionValue =>
          cases conditionValue with
          | word sourceCondition =>
              obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord hbytesInWord hrel.2.1
                  (fun name value hvalue =>
                    hlookup sourceLocals name value hvalue)
                  condition sourceCondition hcondition
              have hcompile : compileProg context
                  (.while condition.toExp body) =
                  .while compiledCondition (compileProg context body) := by
                simp [compileProg, hcompileCondition]
              rw [hcompile] at hcrep
              by_cases hzero : sourceCondition = 0
              · have hzeroResult := compile_full_pan_value_while_source_word_zero_relation_fuel
                  context structs sourceFunctions functions sourceLocals sourceGlobals
                  sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                  baseAddress topAddress bytesInWord (sourceFuel + 1) targetFuel condition
                  body (compileProg context body) sourceCondition sourceCondition
                  exceptionRel hbytesInWord hrel (hlookup sourceLocals) hcondition rfl hzero rfl
                have hsourceEq :
                    PanValueControlResult.normal sourceLocals sourceGlobals sourceMemory =
                      sourceResult := by
                  exact Option.some.inj (hzeroResult.1.symm.trans hsource)
                have hzeroCrep :
                    evalCrepFullProg functions crepPrimitive ffi sharedMem
                      baseAddress topAddress (targetFuel + 1) state
                      (.while compiledCondition (compileProg context body)) =
                      some (.normal state) := by
                  simpa [hcompile] using hzeroResult.2.1
                have hcrepEq : CrepControlResult.normal state = crepResult := by
                  exact Option.some.inj (hzeroCrep.symm.trans hcrep)
                cases hsourceEq
                cases hcrepEq
                exact hzeroResult.2.2
              · cases targetFuel with
                | zero =>
                    have hnonzero' : (sourceCondition == 0) = false := by
                      simpa using hzero
                    simp [evalCrepFullProg, hcrepCondition, hnonzero'] at hcrep
                | succ targetFuel =>
                    have hnonzero : sourceCondition ≠ 0 := hzero
                    have hnonzero' : (sourceCondition == 0) = false := by
                      simpa using hnonzero
                    cases hsourceBody :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord (sourceFuel + 1)
                          sourceLocals sourceGlobals sourceMemory body with
                    | none =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                          evalPanValueExp, hcondition, hnonzero,
                          hsourceBody] at hsource
                    | some sourceBodyResult =>
                        cases hcrepBody :
                            evalCrepFullProg functions crepPrimitive ffi sharedMem
                              baseAddress topAddress (targetFuel + 1) state
                              (compileProg context body) with
                        | none =>
                            simp [evalCrepFullProg, hcrepCondition, hnonzero',
                              hcrepBody] at hcrep
                        | some crepBodyResult =>
                            have hsourceBody' :
                                evalPanValueProgWithPrimitiveCallsAndFfi
                                  primitive sourceHandler structs sourceFunctions
                              baseAddress topAddress bytesInWord (sourceFuel + 1)
                                  sourceLocals sourceGlobals sourceMemory body =
                                  some sourceBodyResult := hsourceBody
                            have hcrepBody' :
                                evalCrepFullProg functions crepPrimitive ffi sharedMem
                              baseAddress topAddress (targetFuel + 1) state
                                  (compileProg context body) = some crepBodyResult :=
                              hcrepBody
                            have hbodyRel := hbody context structs sourceFunctions
                              functions sourceLocals sourceGlobals sourceMemory state
                              primitive sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord (sourceFuel + 1) (targetFuel + 1)
                              exceptionRel sourceBodyResult crepBodyResult hrel
                              hsourceBody' hcrepBody'
                            have hbodySafe' := hbodySafe context structs sourceFunctions
                              functions sourceLocals sourceGlobals sourceMemory state
                              primitive sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord (sourceFuel + 1)
                              (targetFuel + 1) sourceBodyResult
                              crepBodyResult hrel hsourceBody' hcrepBody'
                            cases sourceBodyResult with
                            | normal nextLocals nextGlobals nextMemory =>
                                cases crepBodyResult with
                                | normal nextState =>
                                    have hnextRel :
                                        panValueCrepStateRel structs context nextLocals
                                          nextGlobals nextMemory nextState := by
                                      simpa [panValueCrepControlRel] using hbodyRel
                                    have hsourceLoop :
                                        evalPanValueProgWithPrimitiveCallsAndFfi
                                          primitive sourceHandler structs sourceFunctions
                                          baseAddress topAddress bytesInWord (sourceFuel + 1)
                                          nextLocals nextGlobals nextMemory
                                          (.while condition.toExp body) = some sourceResult := by
                                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hcondition, hnonzero', hsourceBody] using hsource
                                    have hcrepLoop :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1) nextState
                                          (.while compiledCondition (compileProg context body)) =
                                          some crepResult := by
                                      simpa [evalCrepFullProg, hcrepCondition,
                                        hnonzero', hcrepBody] using hcrep
                                    have hcrepLoop' :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1) nextState
                                          (compileProg context (.while condition.toExp body)) =
                                          some crepResult := by
                                      simpa [hcompile] using hcrepLoop
                                    have hloopRel := ih nextLocals nextGlobals nextMemory nextState
                                      targetFuel sourceResult crepResult hnextRel
                                      hsourceLoop hcrepLoop'
                                    have hstep := compile_full_pan_value_while_nonzero_compose_fuel
                                      context structs sourceFunctions functions sourceLocals
                                      sourceGlobals sourceMemory nextLocals nextGlobals
                                      nextMemory state nextState primitive sourceHandler
                                      crepPrimitive ffi sharedMem baseAddress topAddress
                                      bytesInWord (sourceFuel + 1) (targetFuel + 1)
                                      condition.toExp compiledCondition body
                                      (compileProg context body) sourceCondition sourceCondition
                                      sourceResult crepResult hcompileCondition rfl hcondition
                                      hcrepCondition rfl hnonzero hsourceBody' hcrepBody'
                                      hsourceLoop hcrepLoop
                                    have hstep' :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1 + 1) state
                                          (.while compiledCondition (compileProg context body)) =
                                          some crepResult := by
                                      simpa [hcompile] using hstep.2
                                    have hsourceEq := Option.some.inj (hstep.1.symm.trans hsource)
                                    have hcrepEq := Option.some.inj (hstep'.symm.trans hcrep)
                                    cases hsourceEq
                                    cases hcrepEq
                                    exact hloopRel
                                | returned nextState values
                                | raised nextState exception
                                | broke nextState label
                                | continued nextState label
                                | finalFfi nextState event =>
                                    simp [panValueCrepControlRel] at hbodyRel
                            | returned nextLocals nextGlobals nextMemory values =>
                                cases crepBodyResult with
                                | returned nextState crepValues =>
                                    have hsourceEq :
                                        PanValueControlResult.returned nextLocals
                                          nextGlobals nextMemory values = sourceResult := by
                                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hcondition, hnonzero', hsourceBody] using hsource
                                    have hcrepEq :
                                        CrepControlResult.returned nextState crepValues =
                                          crepResult := by
                                      simpa [evalCrepFullProg, hcrepCondition,
                                        hnonzero', hcrepBody] using hcrep
                                    cases hsourceEq
                                    cases hcrepEq
                                    exact hbodyRel
                                | normal nextState
                                | raised nextState exception
                                | broke nextState label
                                | continued nextState label
                                | finalFfi nextState event =>
                                    simp [panValueCrepControlRel] at hbodyRel
                            | raised nextLocals nextGlobals nextMemory exception value =>
                                cases crepBodyResult with
                                | raised nextState exceptionCode =>
                                    have hsourceEq :
                                        PanValueControlResult.raised nextLocals
                                          nextGlobals nextMemory exception value = sourceResult := by
                                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hcondition, hnonzero', hsourceBody] using hsource
                                    have hcrepEq :
                                        CrepControlResult.raised nextState exceptionCode =
                                          crepResult := by
                                      simpa [evalCrepFullProg, hcrepCondition,
                                        hnonzero', hcrepBody] using hcrep
                                    cases hsourceEq
                                    cases hcrepEq
                                    exact hbodyRel
                                | normal nextState
                                | returned nextState values
                                | broke nextState label
                                | continued nextState label
                                | finalFfi nextState event =>
                                    simp [panValueCrepControlRel] at hbodyRel
                            | broke nextLocals nextGlobals nextMemory =>
                                cases crepBodyResult with
                                | broke nextState label =>
                                    have hlabel : label = 0 := hbodySafe'
                                    subst label
                                    have hnextRel :
                                        panValueCrepStateRel structs context nextLocals
                                          nextGlobals nextMemory nextState := by
                                      simpa [panValueCrepControlRel] using hbodyRel
                                    have hstep := compile_full_pan_value_while_break_compose_fuel
                                      context structs sourceFunctions functions sourceLocals
                                      sourceGlobals sourceMemory nextLocals nextGlobals
                                      nextMemory state nextState primitive sourceHandler
                                      crepPrimitive ffi sharedMem baseAddress topAddress
                                      bytesInWord (sourceFuel + 1) (targetFuel + 1)
                                      condition.toExp compiledCondition body
                                      (compileProg context body) sourceCondition sourceCondition
                                      hcompileCondition rfl hcondition hcrepCondition rfl hnonzero
                                      hsourceBody' hcrepBody'
                                    have hstep' :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1 + 1) state
                                          (.while compiledCondition (compileProg context body)) =
                                          some (.normal nextState) := by
                                      simpa [hcompile] using hstep.2
                                    have hsourceEq := Option.some.inj (hstep.1.symm.trans hsource)
                                    have hcrepEq := Option.some.inj (hstep'.symm.trans hcrep)
                                    cases hsourceEq
                                    cases hcrepEq
                                    exact hnextRel
                                | normal nextState
                                | returned nextState values
                                | raised nextState exception
                                | continued nextState label
                                | finalFfi nextState event =>
                                    simp [panValueCrepControlRel] at hbodyRel
                            | continued nextLocals nextGlobals nextMemory =>
                                cases crepBodyResult with
                                | continued nextState label =>
                                    have hlabel : label = 0 := hbodySafe'
                                    subst label
                                    have hnextRel :
                                        panValueCrepStateRel structs context nextLocals
                                          nextGlobals nextMemory nextState := by
                                      simpa [panValueCrepControlRel] using hbodyRel
                                    have hsourceLoop :
                                        evalPanValueProgWithPrimitiveCallsAndFfi
                                          primitive sourceHandler structs sourceFunctions
                                          baseAddress topAddress bytesInWord (sourceFuel + 1)
                                          nextLocals nextGlobals nextMemory
                                          (.while condition.toExp body) = some sourceResult := by
                                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hcondition, hnonzero', hsourceBody] using hsource
                                    have hcrepLoop :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1) nextState
                                          (.while compiledCondition (compileProg context body)) =
                                          some crepResult := by
                                      simpa [evalCrepFullProg, hcrepCondition,
                                        hnonzero', hcrepBody] using hcrep
                                    have hcrepLoop' :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1) nextState
                                          (compileProg context (.while condition.toExp body)) =
                                          some crepResult := by
                                      simpa [hcompile] using hcrepLoop
                                    have hloopRel := ih nextLocals nextGlobals nextMemory nextState
                                      targetFuel sourceResult crepResult hnextRel
                                      hsourceLoop hcrepLoop'
                                    have hstep := compile_full_pan_value_while_continue_compose_fuel
                                      context structs sourceFunctions functions sourceLocals
                                      sourceGlobals sourceMemory nextLocals nextGlobals
                                      nextMemory state nextState primitive sourceHandler
                                      crepPrimitive ffi sharedMem baseAddress topAddress
                                      bytesInWord (sourceFuel + 1) (targetFuel + 1)
                                      condition.toExp compiledCondition body
                                      (compileProg context body) sourceCondition sourceCondition
                                      sourceResult crepResult hcompileCondition rfl hcondition
                                      hcrepCondition rfl hnonzero hsourceBody' hcrepBody'
                                      hsourceLoop hcrepLoop
                                    have hstep' :
                                        evalCrepFullProg functions crepPrimitive ffi sharedMem
                                          baseAddress topAddress (targetFuel + 1 + 1) state
                                          (.while compiledCondition (compileProg context body)) =
                                          some crepResult := by
                                      simpa [hcompile] using hstep.2
                                    have hsourceEq := Option.some.inj (hstep.1.symm.trans hsource)
                                    have hcrepEq := Option.some.inj (hstep'.symm.trans hcrep)
                                    cases hsourceEq
                                    cases hcrepEq
                                    exact hloopRel
                                | normal nextState
                                | returned nextState values
                                | raised nextState exception
                                | broke nextState label
                                | finalFfi nextState event =>
                                    simp [panValueCrepControlRel] at hbodyRel
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    evalPanValueExp, hcondition] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    evalPanValueExp, hcondition] at hsource

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_while_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hbodySafe : PanValueCrepProgramLoopControlSafe body)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.while condition.toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          exact panValueCrepProgramCorrect_while_source_word_pos condition body
            hbody hbodySafe context structs sourceFunctions functions sourceLocals sourceGlobals
            sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
            baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
            sourceResult crepResult (hbytesInWord context bytesInWord)
            (hlookup context) hrel hsource hcrep

end Flapjack
