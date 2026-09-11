import Flapjack.CrepeSourceWordGenericStoreCorrectness
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word correctness for the general `Store` statement.

The general store lowering materializes the address and value in two fresh
temporaries before issuing the flat word store.  This theorem lifts the
source-word expression relation through that lowering for arbitrary source
and target fuel.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_store_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : SourceWordExp α)
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
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramCorrect (.store address.toExp value.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
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
                    (.store address.toExp value.toExp) =
                    some (.normal sourceLocals sourceGlobals
                      (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue))) := by
                have hstoreMemory :
                    panValueStoreWithAccess sourceMemory bytesInWord addressValue
                        (.word valueValue) =
                      some (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue)) := by
                  simp [panValueStoreWithAccess, panValueFlatStoreWords,
                    panValueFlatWords, panValueFlatWordsFuel, panValueFlatOffset,
                    updatePanValueMemory]
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  hsourceAddress, hsourceValue, hstoreMemory]
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
              have hvalueAfter := hstable state baseAddress topAddress
                (context.maxVar + 1) compiledValue valueValue addressValue
                hcrepValue
              have hcompile :
                  compileProg context (.store address.toExp value.toExp) =
                    nestedDecs [context.maxVar + 1, context.maxVar + 2]
                      [compiledAddress, compiledValue]
                      (crepNestedSeq
                        (stores (.var (context.maxVar + 1))
                          [.var (context.maxVar + 2)] 0 context.bytesInWord)) := by
                simp [compileProg, hcompileAddress, hcompileValue, freshNames,
                  nestedDecs, stores, crepNestedSeq]
              have hmemory := panValueCrepMemoryRel_update_word
                sourceMemory state.memory addressValue valueValue hrel.2.2
              have htargetRel :
                  panValueCrepStateRel structs context sourceLocals sourceGlobals
                    (updatePanValueMemory sourceMemory addressValue
                      (.word valueValue))
                    { state with memory :=
                        updateMemory state.memory addressValue valueValue } := by
                exact ⟨hrel.1, hrel.2.1, by
                  simpa [updateMemory] using hmemory⟩
              rw [hcompile] at hcrep
              cases targetFuel with
              | zero =>
                  simp [nestedDecs, evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [nestedDecs, evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [nestedDecs, evalCrepFullProg] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              simp [nestedDecs, crepNestedSeq, stores,
                                evalCrepFullProg, evalCrepFullExp] at hcrep
                          | succ targetFuel =>
                              have hrestore :
                                  restoreCrepLocal
                                      (restoreCrepLocal
                                        (updateCrepLocal
                                          (updateCrepLocal state.locals
                                            (context.maxVar + 1) addressValue)
                                          (context.maxVar + 2) valueValue)
                                        (context.maxVar + 2)
                                        (state.locals (context.maxVar + 2)))
                                    (context.maxVar + 1)
                                    (state.locals (context.maxVar + 1)) =
                                  state.locals := by
                                funext current
                                by_cases haddress :
                                    current = context.maxVar + 1
                                · simp [restoreCrepLocal, haddress]
                                by_cases hvalue : current = context.maxVar + 2
                                · simp [restoreCrepLocal, hvalue]
                                · simp [restoreCrepLocal, updateCrepLocal,
                                    haddress, hvalue]
                              have htargetExpected :
                                  evalCrepFullProg functions crepPrimitive ffi
                                      sharedMem baseAddress topAddress
                                      (targetFuel + 4) state
                                      (compileProg context
                                        (.store address.toExp value.toExp)) =
                                    some (.normal
                                      (CrepState.mk state.locals
                                        (updateMemory state.memory addressValue valueValue))) := by
                                rw [hcompile]
                                simp [nestedDecs, crepNestedSeq, stores,
                                  evalCrepFullProg, evalCrepFullExp,
                                  hcrepAddress, hvalueAfter, updateCrepLocal,
                                  restoreCrepResult, hrestore, Nat.add_assoc]
                              have hsourceEq :=
                                Option.some.inj (hsourceExpected.symm.trans hsource)
                              have hcrepForRelation :
                                  evalCrepFullProg functions crepPrimitive ffi
                                      sharedMem baseAddress topAddress
                                      (targetFuel + 4) state
                                      (compileProg context
                                        (.store address.toExp value.toExp)) =
                                    some crepResult := by
                                simpa [hcompile, Nat.add_assoc] using hcrep
                              have hcrepEq :=
                                Option.some.inj
                                  (htargetExpected.symm.trans hcrepForRelation)
                              have hcontrol :
                                  panValueCrepControlRel structs context exceptionRel
                                    (.normal sourceLocals sourceGlobals
                                      (updatePanValueMemory sourceMemory
                                        addressValue (.word valueValue)))
                                    (.normal
                                      (CrepState.mk state.locals
                                        (updateMemory state.memory addressValue valueValue))) := by
                                exact ⟨htargetRel.1, htargetRel.2.1,
                                  htargetRel.2.2⟩
                              rw [hsourceEq, hcrepEq] at hcontrol
                              exact hcontrol

end Flapjack
