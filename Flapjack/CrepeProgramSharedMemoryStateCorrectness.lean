import Flapjack.CrepeProgramSharedMemoryCorrectness
import Flapjack.CrepeProgramRelation

namespace Flapjack

theorem panValueCrepProgramStateCorrect_shMemStore_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (address value : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value)
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue : α),
      sharedMem (storeMemOp size) (context.maxVar + 1) addressValue
        { state with
          locals := updateCrepLocal state.locals (context.maxVar + 1) valueValue } =
        some targetState →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))
        { targetState with
          locals := restoreCrepLocal targetState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) :
    PanValueCrepProgramStateCorrect
      (.shMemStore size address.toExp value.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hstateExpFromLegacy :
      ∀ (sourceExpression : SourceWordExp α) (sourceValue : α)
        (compiled : CrepExp α) (targetState : CrepState α),
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord sourceExpression.toExp =
          some (.word sourceValue) →
        compileExp context sourceExpression.toExp = ([compiled], .one) →
        evalCrepFullExp targetState.locals targetState.memory
          baseAddress topAddress compiled = some sourceValue →
        evalCrepFullExpState targetState baseAddress topAddress compiled =
          some sourceValue := by
    intro sourceExpression sourceValue compiled targetState hsourceExpression
      hcompileExpression hcompiledExpression
    obtain ⟨compiled', hcompile', hnoGlobal⟩ :=
      compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (fun current value hvalue =>
          hlookup context sourceLocals current value hvalue)
        sourceExpression sourceValue hsourceExpression
    have hcompiledEq : compiled = compiled' := by
      have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
        hcompileExpression.symm.trans hcompile'
      exact (List.cons.inj (congrArg Prod.fst hpair)).1
    have hcompiled' :
        evalCrepFullExp targetState.locals targetState.memory
          baseAddress topAddress compiled' = some sourceValue := by
      simpa [hcompiledEq] using hcompiledExpression
    rw [hcompiledEq]
    exact (evalCrepFullExpState_eq_of_noGlobal targetState
      baseAddress topAddress compiled' hnoGlobal).trans hcompiled'
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue' =>
          obtain ⟨addressValue, haddressWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            address addressValue' haddress
          have hsourceAddress :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord address.toExp =
                some (.word addressValue) := by
            rw [haddress, haddressWord]
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord value.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                hvalue] at hsource
          | some valueValue' =>
              obtain ⟨valueValue, hvalueWord⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun name value hvalue =>
                  hlookup context sourceLocals name value hvalue)
                value valueValue' hvalue
              have hsourceValue :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord value.toExp =
                    some (.word valueValue) := by
                rw [hvalue, hvalueWord]
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.shMemStore size address.toExp value.toExp) =
                    some (.normal sourceLocals sourceGlobals
                      (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue))) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  hsourceAddress, hsourceValue]
              obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun name value hvalue =>
                    hlookup context sourceLocals name value hvalue)
                  address addressValue hsourceAddress
              obtain ⟨compiledValue, hcompileValue, hcrepValue⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun name value hvalue =>
                    hlookup context sourceLocals name value hvalue)
                  value valueValue hsourceValue
              have hfirstAddress :
                  firstCompiledExp context address.toExp = some compiledAddress := by
                simp [firstCompiledExp, hcompileAddress]
              have hfirstValue :
                  firstCompiledExp context value.toExp = some compiledValue := by
                simp [firstCompiledExp, hcompileValue]
              have hcompileProg :
                  compileProg context
                      (.shMemStore size address.toExp value.toExp) =
                    nestedDecs [context.maxVar + 1] [compiledValue]
                      (.shMem (storeMemOp size) (context.maxVar + 1)
                        compiledAddress) := by
                simp [compileProg, hfirstAddress, hfirstValue, nestedDecs]
              rw [hcompileProg] at hcrep
              have hcrepAddressAfter := hstable state baseAddress topAddress
                (context.maxVar + 1) compiledAddress addressValue valueValue
                hcrepAddress
              have hcrepValueState := hstateExpFromLegacy value valueValue
                compiledValue state hsourceValue hcompileValue hcrepValue
              let stateAfterValue : CrepState α :=
                { state with
                  locals := updateCrepLocal state.locals
                    (context.maxVar + 1) valueValue }
              have hcrepAddressAfterState := hstateExpFromLegacy address
                addressValue compiledAddress stateAfterValue hsourceAddress
                hcompileAddress hcrepAddressAfter
              dsimp [stateAfterValue] at hcrepAddressAfterState
              cases targetFuel with
              | zero =>
                  simp [nestedDecs, evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [nestedDecs, evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases hshared : sharedMem (storeMemOp size)
                          (context.maxVar + 1) addressValue
                          { state with
                            locals := updateCrepLocal state.locals
                              (context.maxVar + 1) valueValue } with
                      | none =>
                          simp [nestedDecs, evalCrepFullProgState,
                            hcrepValueState, hcrepAddressAfterState, hshared] at hcrep
                      | some targetState =>
                          have htargetRel := hsharedRel context structs
                            sourceLocals sourceGlobals sourceMemory state targetState
                            crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord addressValue valueValue hshared
                          have htargetExpected :
                              evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                baseAddress topAddress (targetFuel + 2) state
                                (compileProg context
                                  (.shMemStore size address.toExp value.toExp)) =
                              some (.normal
                                { targetState with
                                  locals := restoreCrepLocal targetState.locals
                                    (context.maxVar + 1)
                                    (state.locals (context.maxVar + 1)) }) := by
                            rw [hcompileProg]
                            simp [nestedDecs, evalCrepFullProgState,
                              hcrepValueState, hcrepAddressAfterState, hshared,
                              restoreCrepResult]
                          have hsourceEq :=
                            Option.some.inj (hsourceExpected.symm.trans hsource)
                          have hcrepForRelation :
                              evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                baseAddress topAddress (targetFuel + 2) state
                                (compileProg context
                                  (.shMemStore size address.toExp value.toExp)) =
                                some crepResult := by
                            simpa [hcompileProg, Nat.add_assoc] using hcrep
                          have hcrepEq :=
                            Option.some.inj (htargetExpected.symm.trans hcrepForRelation)
                          have hcontrol :
                              panValueCrepControlRel structs context exceptionRel
                                (.normal sourceLocals sourceGlobals
                                  (updatePanValueMemory sourceMemory addressValue
                                    (.word valueValue)))
                                (.normal
                                  ({ targetState with
                                    locals := restoreCrepLocal targetState.locals
                                      (context.maxVar + 1)
                                      (state.locals (context.maxVar + 1)) } : CrepState α)) := by
                            simpa [panValueCrepControlRel] using htargetRel
                          rw [hsourceEq, hcrepEq] at hcontrol
                          exact hcontrol

end Flapjack
