import Flapjack.CrepeSharedMemoryRelation
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word correctness for shared-memory stores.

The low-level shared-memory relation already accounts for the handler
transition.  This boundary supplies the expression compilation, the fresh
temporary used by `compileProg`, and the post-handler state relation needed by
the compositional program predicate.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_shMemStore_source_word
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
    PanValueCrepProgramCorrect
      (.shMemStore size address.toExp value.toExp) := by
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
              cases targetFuel with
              | zero =>
                  simp [nestedDecs, evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [nestedDecs, evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases hshared : sharedMem (storeMemOp size)
                          (context.maxVar + 1) addressValue
                          { state with
                            locals := updateCrepLocal state.locals
                              (context.maxVar + 1) valueValue } with
                      | none =>
                          simp [nestedDecs, evalCrepFullProg, hcrepValue,
                            hcrepAddressAfter, hshared] at hcrep
                      | some targetState =>
                          have htargetRel := hsharedRel context structs
                            sourceLocals sourceGlobals sourceMemory state targetState
                            crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord addressValue valueValue hshared
                          have hresult :=
                            compile_full_pan_value_shMemStore_word_relation
                              context structs sourceFunctions functions sourceLocals
                              sourceGlobals sourceMemory state targetState primitive
                              sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord targetFuel exceptionRel size
                              addressValue valueValue address.toExp value.toExp
                              compiledAddress compiledValue hsourceAddress hsourceValue
                              hfirstAddress hfirstValue hcrepAddressAfter hcrepValue
                              hshared htargetRel
                          have hsourceEq :=
                            Option.some.inj (hsourceExpected.symm.trans hsource)
                          have hcrepForRelation :
                              evalCrepFullProg functions crepPrimitive ffi sharedMem
                                baseAddress topAddress (targetFuel + 2) state
                                (compileProg context
                                  (.shMemStore size address.toExp value.toExp)) =
                                some crepResult := by
                            simpa [hcompileProg, Nat.add_assoc] using hcrep
                          have hcrepEq :=
                            Option.some.inj (hresult.2.1.symm.trans hcrepForRelation)
                          have hcontrol := hresult.2.2
                          rw [hsourceEq, hcrepEq] at hcontrol
                          exact hcontrol

end Flapjack
