import Flapjack.CrepeProgramExtCallCorrectness
import Flapjack.CrepeExtCallInversion
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeExpressionStability

/-!
Correctness for an ExtCall whose four arguments are scalar source-word
expressions.  The expression relation supplies one lowered Crep expression
and its evaluation for each argument.  Since later arguments are evaluated
after earlier temporary bindings, `hstable` records the required freshness/
non-interference fact explicitly.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_extCall_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : SourceWordExp α)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
      (ffi : CrepFfiHandler α), panValueCrepExtCallCorrect sourceHandler ffi)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hfresh : ∀ (context : CompileContext α) (expression : SourceWordExp α)
      (compiled : CrepExp α),
      compileExp context expression.toExp = ([compiled], .one) →
      ∀ temporary, context.maxVar < temporary →
        temporary ∉ crepExpVars compiled) :
    PanValueCrepProgramCorrect
      (.extCall function configuration.toExp configurationLength.toExp
        array.toExp arrayLength.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      have hsource' :
          evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.extCall function configuration.toExp configurationLength.toExp
              array.toExp arrayLength.toExp) = some sourceResult := by
        simpa [Nat.succ_eq_add_one] using hsource
      obtain ⟨values, hvalues, hvalueResult⟩ := evalPanValueExtCall_values
        primitive sourceHandler structs sourceFunctions baseAddress topAddress
        bytesInWord sourceFuel sourceLocals sourceGlobals sourceMemory function
        configuration.toExp configurationLength.toExp array.toExp
        arrayLength.toExp sourceResult hsource'
      obtain ⟨configurationValue, configurationLengthValue, arrayValue,
        arrayLengthValue, sourceLocals', hwordValues, hsourceHandler, hsourceResult⟩ :=
        evalPanValueExtCallValues_word_inv sourceHandler function sourceLocals
          sourceGlobals sourceMemory values sourceResult hvalueResult
      cases hwordValues
      cases hsourceResult
      obtain ⟨hconfigurationSource, hconfigurationLengthSource, harraySource,
        harrayLengthSource⟩ := evalPanValueExps_four_word_projection_all
        structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
        bytesInWord configuration.toExp configurationLength.toExp array.toExp
        arrayLength.toExp configurationValue configurationLengthValue arrayValue
        arrayLengthValue hvalues
      obtain ⟨configurationCompiled, hcompileConfiguration,
        hconfigurationEval⟩ := compileSourceWordExp_relation
        context structs sourceLocals sourceGlobals sourceMemory state.locals
        state.memory baseAddress topAddress bytesInWord
        (hbytesInWord context bytesInWord) hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        configuration configurationValue hconfigurationSource
      obtain ⟨configurationLengthCompiled, hcompileConfigurationLength,
        hconfigurationLengthEval⟩ := compileSourceWordExp_relation
        context structs sourceLocals sourceGlobals sourceMemory state.locals
        state.memory baseAddress topAddress bytesInWord
        (hbytesInWord context bytesInWord) hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        configurationLength configurationLengthValue hconfigurationLengthSource
      obtain ⟨arrayCompiled, hcompileArray, harrayEval⟩ :=
        compileSourceWordExp_relation context structs sourceLocals sourceGlobals
          sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
          (hbytesInWord context bytesInWord) hrel.2.1
          (fun name value hvalue => hlookup context sourceLocals name value hvalue)
          array arrayValue harraySource
      obtain ⟨arrayLengthCompiled, hcompileArrayLength, harrayLengthEval⟩ :=
        compileSourceWordExp_relation context structs sourceLocals sourceGlobals
          sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
          (hbytesInWord context bytesInWord) hrel.2.1
          (fun name value hvalue => hlookup context sourceLocals name value hvalue)
          arrayLength arrayLengthValue harrayLengthSource
      have hfirstConfiguration :
          firstCompiledExp context configuration.toExp =
            some configurationCompiled := by
        simp [firstCompiledExp, hcompileConfiguration]
      have hfirstConfigurationLength :
          firstCompiledExp context configurationLength.toExp =
            some configurationLengthCompiled := by
        simp [firstCompiledExp, hcompileConfigurationLength]
      have hfirstArray : firstCompiledExp context array.toExp = some arrayCompiled := by
        simp [firstCompiledExp, hcompileArray]
      have hfirstArrayLength :
          firstCompiledExp context arrayLength.toExp = some arrayLengthCompiled := by
        simp [firstCompiledExp, hcompileArrayLength]
      have hcompile :
          compileProg context
              (.extCall function configuration.toExp configurationLength.toExp
                array.toExp arrayLength.toExp) =
            .dec (context.maxVar + 1) configurationCompiled
              (.dec (context.maxVar + 2) configurationLengthCompiled
                (.dec (context.maxVar + 3) arrayCompiled
                  (.dec (context.maxVar + 4) arrayLengthCompiled
                    (.extCall function (context.maxVar + 1) (context.maxVar + 2)
                      (context.maxVar + 3) (context.maxVar + 4))))) := by
        simpa [nestedDecs] using
          (compileProg_extCall_of_compiled context function configuration.toExp
            configurationLength.toExp array.toExp arrayLength.toExp
            configurationCompiled configurationLengthCompiled arrayCompiled
            arrayLengthCompiled hfirstConfiguration hfirstConfigurationLength
            hfirstArray hfirstArrayLength)
      cases targetFuel with
      | zero =>
          rw [hcompile] at hcrep
          simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompile] at hcrep
              simp [evalCrepFullProg] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompile] at hcrep
                  simp [evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompile] at hcrep
                      simp [evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompile] at hcrep
                          simp [evalCrepFullProg] at hcrep
                      | succ targetFuel =>
                          have hconfigurationLengthFresh := hfresh context
                            configurationLength configurationLengthCompiled
                            hcompileConfigurationLength (context.maxVar + 1)
                            (by omega)
                          have harrayFresh := hfresh context array arrayCompiled
                            hcompileArray (context.maxVar + 1) (by omega)
                          have harrayFresh' := hfresh context array arrayCompiled
                            hcompileArray (context.maxVar + 2) (by omega)
                          have harrayLengthFresh := hfresh context arrayLength
                            arrayLengthCompiled hcompileArrayLength
                            (context.maxVar + 1) (by omega)
                          have harrayLengthFresh' := hfresh context arrayLength
                            arrayLengthCompiled hcompileArrayLength
                            (context.maxVar + 2) (by omega)
                          have harrayLengthFresh'' := hfresh context arrayLength
                            arrayLengthCompiled hcompileArrayLength
                            (context.maxVar + 3) (by omega)
                          have hconfigurationLengthEval' :=
                            evalCrepFullExp_update_of_not_mem state.locals state.memory
                              baseAddress topAddress configurationLengthCompiled
                              (context.maxVar + 1) configurationLengthValue
                              configurationValue hconfigurationLengthFresh
                              hconfigurationLengthEval
                          have harrayEval' :=
                            evalCrepFullExp_update_of_not_mem state.locals state.memory
                              baseAddress topAddress arrayCompiled
                              (context.maxVar + 1) arrayValue configurationValue
                              harrayFresh harrayEval
                          have harrayEval'' :=
                            evalCrepFullExp_update_of_not_mem
                              (updateCrepLocal state.locals (context.maxVar + 1)
                                configurationValue) state.memory
                              baseAddress topAddress arrayCompiled
                              (context.maxVar + 2) arrayValue configurationLengthValue
                              harrayFresh' harrayEval'
                          have harrayLengthEval' :=
                            evalCrepFullExp_update_of_not_mem state.locals state.memory
                              baseAddress topAddress arrayLengthCompiled
                              (context.maxVar + 1) arrayLengthValue configurationValue
                              harrayLengthFresh harrayLengthEval
                          have harrayLengthEval'' :=
                            evalCrepFullExp_update_of_not_mem
                              (updateCrepLocal state.locals (context.maxVar + 1)
                                configurationValue) state.memory
                              baseAddress topAddress arrayLengthCompiled
                              (context.maxVar + 2) arrayLengthValue configurationLengthValue
                              harrayLengthFresh' harrayLengthEval'
                          have harrayLengthEval''' :=
                            evalCrepFullExp_update_of_not_mem
                              (updateCrepLocal
                                (updateCrepLocal state.locals (context.maxVar + 1)
                                  configurationValue)
                                (context.maxVar + 2) configurationLengthValue) state.memory
                              baseAddress topAddress arrayLengthCompiled
                              (context.maxVar + 3) arrayLengthValue arrayValue
                              harrayLengthFresh'' harrayLengthEval''
                          let callLocals : Nat → Option α :=
                            updateCrepLocal
                              (updateCrepLocal
                                (updateCrepLocal
                                  (updateCrepLocal state.locals (context.maxVar + 1)
                                    configurationValue)
                                  (context.maxVar + 2) configurationLengthValue)
                                (context.maxVar + 3) arrayValue)
                              (context.maxVar + 4) arrayLengthValue
                          let callState : CrepState α := { state with locals := callLocals }
                          cases hcall : ffi function configurationValue
                              configurationLengthValue arrayValue arrayLengthValue callState with
                          | none =>
                              rw [compileProg_extCall_of_compiled context function
                                configuration.toExp configurationLength.toExp array.toExp
                                arrayLength.toExp configurationCompiled
                                configurationLengthCompiled arrayCompiled
                                arrayLengthCompiled hfirstConfiguration
                                hfirstConfigurationLength hfirstArray hfirstArrayLength] at hcrep
                              simp [nestedDecs, evalCrepFullProg, updateCrepLocal,
                                callState, callLocals,
                                hconfigurationEval, hconfigurationLengthEval', harrayEval'',
                                harrayLengthEval''', hcall] at hcrep
                          | some result =>
                              obtain ⟨state', hreturned, hstate⟩ :=
                                hffi sourceHandler ffi context structs sourceLocals
                                  sourceLocals' sourceGlobals sourceMemory state function
                                  configurationValue configurationLengthValue arrayValue
                                  arrayLengthValue result hsourceHandler
                                  (by simpa [callState, callLocals] using hcall)
                              cases hreturned
                              have hsim := compile_full_pan_value_extCall_simulation
                                context structs sourceFunctions functions sourceLocals
                                sourceLocals' sourceGlobals sourceMemory state state'
                                primitive crepPrimitive ffi sharedMem sourceHandler
                                baseAddress topAddress bytesInWord targetFuel function
                                configuration.toExp configurationLength.toExp array.toExp
                                arrayLength.toExp configurationCompiled
                                configurationLengthCompiled arrayCompiled arrayLengthCompiled
                                configurationValue configurationLengthValue arrayValue
                                arrayLengthValue hfirstConfiguration
                                hfirstConfigurationLength hfirstArray hfirstArrayLength
                                (by simp [evalPanValueExps,
                                  evalPanValueExp.evalPanValueExps,
                                  hconfigurationSource, hconfigurationLengthSource,
                                  harraySource, harrayLengthSource])
                                hconfigurationEval hconfigurationLengthEval'
                                harrayEval'' harrayLengthEval'''
                                hsourceHandler (by simpa [callState, callLocals] using hcall)
                              have hcrep' :
                                  evalCrepFullProg functions crepPrimitive ffi sharedMem
                                    baseAddress topAddress (targetFuel + 5) state
                                    (compileProg context
                                      (.extCall function configuration.toExp
                                        configurationLength.toExp array.toExp
                                        arrayLength.toExp)) = some crepResult := by
                                simpa [Nat.add_assoc] using hcrep
                              have hcrepEq := Option.some.inj
                                (hsim.1.symm.trans hcrep')
                              cases hcrepEq
                              simpa [panValueCrepControlRel] using hstate

end Flapjack
