import Flapjack.CrepeFfiRelation
import Flapjack.CrepeProgramRelation

/-!
The closed-constant external-call case of the source-to-Crep correctness
induction.  The source evaluator has a normal FFI boundary, so the
correspondence premise requires the target FFI result to be returned and
supplies the post-call source/Crep state relation.  Final target events are
therefore not silently identified with a normal source result.
-/

namespace Flapjack

def panValueCrepExtCallCorrectAt
    (temporaryBase : Nat) (sourceHandler : PanValueFfiHandler α)
    (ffi : CrepFfiHandler α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceLocals' sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (function : FunName) (configuration configurationLength array arrayLength : α)
    (result : CrepFfiResult α),
    sourceHandler function configuration configurationLength array arrayLength
        sourceLocals = some sourceLocals' →
    ffi function configuration configurationLength array arrayLength
        ({ state with
          locals :=
              updateCrepLocal
                (updateCrepLocal
                  (updateCrepLocal
                    (updateCrepLocal state.locals (temporaryBase + 1) configuration)
                    (temporaryBase + 2) configurationLength)
                  (temporaryBase + 3) array)
                (temporaryBase + 4) arrayLength }) = some result →
    ∃ state', result = .returned state' ∧
      panValueCrepStateRel structs context sourceLocals' sourceGlobals
        sourceMemory (restoreCrepFfiTemps state' state temporaryBase)

def panValueCrepExtCallCorrect
    (sourceHandler : PanValueFfiHandler α) (ffi : CrepFfiHandler α) : Prop :=
  panValueCrepExtCallCorrectAt 0 sourceHandler ffi

theorem panValueCrepProgramCorrect_extCall_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
      (ffi : CrepFfiHandler α), panValueCrepExtCallCorrect sourceHandler ffi) :
    PanValueCrepProgramCorrect
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength)) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hsourceHandler : sourceHandler function configuration configurationLength
          array arrayLength sourceLocals with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExps,
            evalPanValueExp.evalPanValueExps, evalPanValueExp, hsourceHandler] at hsource
      | some sourceLocals' =>
          have hsourceResult :
              PanValueControlResult.normal sourceLocals' sourceGlobals sourceMemory =
                sourceResult := by
            have hsource' := hsource
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExps,
              evalPanValueExp.evalPanValueExps, evalPanValueExp, hsourceHandler] at hsource'
            exact hsource'
          cases hsourceResult
          have hcompile :
              compileProg context
                (.extCall function (.const configuration)
                  (.const configurationLength) (.const array) (.const arrayLength)) =
                .dec 1 (.const configuration)
                  (.dec 2 (.const configurationLength)
                    (.dec 3 (.const array)
                      (.dec 4 (.const arrayLength)
                        (.extCall function 1 2 3 4)))) := by
            simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
              maxCrepExpVar]
          cases targetFuel with
          | zero =>
              rw [hcompile] at hcrep
              simp [evalCrepFullProg] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompile] at hcrep
                  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompile] at hcrep
                      simp [evalCrepFullProg, evalCrepFullExp] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompile] at hcrep
                          simp [evalCrepFullProg, evalCrepFullExp] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompile] at hcrep
                              simp [evalCrepFullProg, evalCrepFullExp] at hcrep
                          | succ targetFuel =>
                          have hconfiguration :
                              firstCompiledExp context (.const configuration) =
                                some (.const configuration) := by
                            simp [firstCompiledExp, compileExp]
                          have hconfigurationLength :
                              firstCompiledExp context (.const configurationLength) =
                                some (.const configurationLength) := by
                            simp [firstCompiledExp, compileExp]
                          have harray :
                              firstCompiledExp context (.const array) = some (.const array) := by
                            simp [firstCompiledExp, compileExp]
                          have harrayLength :
                              firstCompiledExp context (.const arrayLength) =
                                some (.const arrayLength) := by
                            simp [firstCompiledExp, compileExp]
                          have hconfigurationValue :
                              evalCrepFullExp state.locals state.memory baseAddress topAddress
                                (.const configuration) = some configuration := by
                            simp [evalCrepFullExp]
                          have hconfigurationLengthValue :
                              evalCrepFullExp
                                (updateCrepLocal state.locals 1 configuration)
                                state.memory baseAddress topAddress
                                (.const configurationLength) = some configurationLength := by
                            simp [evalCrepFullExp]
                          have harrayValue :
                              evalCrepFullExp
                                (updateCrepLocal
                                  (updateCrepLocal state.locals 1 configuration)
                                  2 configurationLength)
                                state.memory baseAddress topAddress
                                (.const array) = some array := by
                            simp [evalCrepFullExp]
                          have harrayLengthValue :
                              evalCrepFullExp
                                (updateCrepLocal
                                  (updateCrepLocal
                                    (updateCrepLocal state.locals 1 configuration)
                                    2 configurationLength)
                                  3 array)
                                state.memory baseAddress topAddress
                                (.const arrayLength) = some arrayLength := by
                            simp [evalCrepFullExp]
                          cases hcall : ffi function configuration configurationLength array
                              arrayLength
                              ({ state with
                                locals :=
                                  updateCrepLocal
                                    (updateCrepLocal
                                      (updateCrepLocal
                                        (updateCrepLocal state.locals 1
                                          configuration)
                                        2 configurationLength)
                                      3 array)
                                    4 arrayLength }) with
                          | none =>
                              rw [compileProg_extCall_of_compiled context function
                                (.const configuration) (.const configurationLength)
                                (.const array) (.const arrayLength)
                                (.const configuration) (.const configurationLength)
                                (.const array) (.const arrayLength)
                                hconfiguration hconfigurationLength harray harrayLength] at hcrep
                              simp [nestedDecs, evalCrepFullProg, updateCrepLocal,
                                hconfigurationValue, hconfigurationLengthValue,
                                harrayValue, harrayLengthValue, hcall,
                                maxCrepExpVar] at hcrep
                          | some result =>
                              obtain ⟨state', hreturned, hstate⟩ :=
                                hffi sourceHandler ffi context structs sourceLocals
                                  sourceLocals' sourceGlobals sourceMemory state function
                                  configuration configurationLength array arrayLength result
                                  hsourceHandler hcall
                              cases hreturned
                              have hsim := compile_full_pan_value_extCall_simulation
                                context structs sourceFunctions functions sourceLocals
                                sourceLocals' sourceGlobals sourceMemory state state'
                                primitive crepPrimitive ffi sharedMem sourceHandler
                                baseAddress topAddress bytesInWord targetFuel function
                                (.const configuration) (.const configurationLength)
                                (.const array) (.const arrayLength)
                                (.const configuration) (.const configurationLength)
                                (.const array) (.const arrayLength)
                                configuration configurationLength array arrayLength
                                hconfiguration hconfigurationLength harray harrayLength
                                (by simp [evalPanValueExps,
                                  evalPanValueExp.evalPanValueExps, evalPanValueExp])
                                hconfigurationValue
                                (by simpa [maxCrepExpVar, crepExpVars, List.foldl]
                                  using hconfigurationLengthValue)
                                (by simpa [maxCrepExpVar, crepExpVars, List.foldl]
                                  using harrayValue)
                                (by simpa [maxCrepExpVar, crepExpVars, List.foldl]
                                  using harrayLengthValue)
                                hsourceHandler
                                (by simpa [maxCrepExpVar, crepExpVars, List.foldl]
                                  using hcall)
                              have hcrep' :
                                  evalCrepFullProg functions crepPrimitive ffi sharedMem
                                    baseAddress topAddress (targetFuel + 5) state
                                    (compileProg context
                                      (.extCall function (.const configuration)
                                        (.const configurationLength) (.const array)
                                        (.const arrayLength))) = some crepResult := by
                                simpa [Nat.add_assoc] using hcrep
                              have hcrepEq := Option.some.inj
                                (hsim.1.symm.trans hcrep')
                              cases hcrepEq
                              simpa [panValueCrepControlRel, maxCrepExpVar,
                                crepExpVars, List.foldl] using hstate

theorem panValueCrepProgramStateCorrect_extCall_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
      (ffi : CrepFfiHandler α), panValueCrepExtCallCorrect sourceHandler ffi) :
    PanValueCrepProgramStateCorrect
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength)) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hsourceHandler : sourceHandler function configuration configurationLength
          array arrayLength sourceLocals with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExps,
            evalPanValueExp.evalPanValueExps, evalPanValueExp, hsourceHandler] at hsource
      | some sourceLocals' =>
          have hsourceResult :
              PanValueControlResult.normal sourceLocals' sourceGlobals sourceMemory =
                sourceResult := by
            have hsource' := hsource
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExps,
              evalPanValueExp.evalPanValueExps, evalPanValueExp, hsourceHandler] at hsource'
            exact hsource'
          cases hsourceResult
          have hcompile :
              compileProg context
                (.extCall function (.const configuration)
                  (.const configurationLength) (.const array) (.const arrayLength)) =
                .dec 1 (.const configuration)
                  (.dec 2 (.const configurationLength)
                    (.dec 3 (.const array)
                      (.dec 4 (.const arrayLength)
                        (.extCall function 1 2 3 4)))) := by
            simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
              maxCrepExpVar]
          cases targetFuel with
          | zero =>
              rw [hcompile] at hcrep
              simp [evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompile] at hcrep
                  simp [evalCrepFullProgState, evalCrepFullExpState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompile] at hcrep
                      simp [evalCrepFullProgState, evalCrepFullExpState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompile] at hcrep
                          simp [evalCrepFullProgState, evalCrepFullExpState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompile] at hcrep
                              simp [evalCrepFullProgState, evalCrepFullExpState] at hcrep
                          | succ targetFuel =>
                              have hconfigurationValue :
                                  evalCrepFullExpState state baseAddress topAddress
                                    (.const configuration) = some configuration := by
                                simp [evalCrepFullExpState]
                              have hconfigurationLengthValue :
                                  evalCrepFullExpState
                                    { state with
                                      locals := updateCrepLocal state.locals
                                        1 configuration }
                                    baseAddress topAddress (.const configurationLength) =
                                    some configurationLength := by
                                simp [evalCrepFullExpState]
                              have harrayValue :
                                  evalCrepFullExpState
                                    { state with
                                      locals := updateCrepLocal
                                        (updateCrepLocal state.locals
                                          1 configuration)
                                        2 configurationLength }
                                    baseAddress topAddress (.const array) = some array := by
                                simp [evalCrepFullExpState]
                              have harrayLengthValue :
                                  evalCrepFullExpState
                                    { state with
                                      locals := updateCrepLocal
                                        (updateCrepLocal
                                          (updateCrepLocal state.locals
                                            1 configuration)
                                          2 configurationLength)
                                        3 array }
                                    baseAddress topAddress (.const arrayLength) =
                                    some arrayLength := by
                                simp [evalCrepFullExpState]
                              cases hcall : ffi function configuration configurationLength array
                                  arrayLength
                                  ({ state with
                                    locals :=
                                      updateCrepLocal
                                        (updateCrepLocal
                                          (updateCrepLocal
                                            (updateCrepLocal state.locals 1
                                              configuration)
                                            2 configurationLength)
                                          3 array)
                                        4 arrayLength }) with
                              | none =>
                                  rw [compileProg_extCall_of_compiled context function
                                    (.const configuration) (.const configurationLength)
                                    (.const array) (.const arrayLength)
                                    (.const configuration) (.const configurationLength)
                                    (.const array) (.const arrayLength)
                                    (by simp [firstCompiledExp, compileExp])
                                    (by simp [firstCompiledExp, compileExp])
                                    (by simp [firstCompiledExp, compileExp])
                                    (by simp [firstCompiledExp, compileExp])] at hcrep
                                  simp [nestedDecs, evalCrepFullProgState,
                                    evalCrepFullExpState, updateCrepLocal,
                                    hconfigurationValue, hcall,
                                    maxCrepExpVar] at hcrep
                              | some result =>
                                  obtain ⟨state', hreturned, hstate⟩ :=
                                    hffi sourceHandler ffi context structs sourceLocals
                                      sourceLocals' sourceGlobals sourceMemory state function
                                      configuration configurationLength array arrayLength result
                                      hsourceHandler hcall
                                  cases hreturned
                                  have htargetExpected :
                                      evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                        baseAddress topAddress (targetFuel + 5) state
                                        (compileProg context
                                          (.extCall function (.const configuration)
                                            (.const configurationLength) (.const array)
                                            (.const arrayLength))) =
                                      some (.normal
                                        (restoreCrepFfiTemps state' state 0)) := by
                                    rw [hcompile]
                                    simp [evalCrepFullProgState, evalCrepFullExpState,
                                      updateCrepLocal, hconfigurationValue,
                                      hcall, restoreCrepResult,
                                      restoreCrepFfiTemps]
                                  have hcrep' :
                                      evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                        baseAddress topAddress (targetFuel + 5) state
                                        (compileProg context
                                          (.extCall function (.const configuration)
                                            (.const configurationLength) (.const array)
                                            (.const arrayLength))) = some crepResult := by
                                    simpa [Nat.add_assoc] using hcrep
                                  have hcrepEq := Option.some.inj
                                    (htargetExpected.symm.trans hcrep')
                                  cases hcrepEq
                                  simpa [panValueCrepControlRel] using hstate

end Flapjack
