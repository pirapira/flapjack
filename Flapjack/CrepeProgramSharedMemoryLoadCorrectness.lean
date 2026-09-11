import Flapjack.CrepeSharedMemoryRelation
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word correctness for shared-memory loads.

The source operation is a word assignment to an existing local.  This bridge
connects its source-side validity check and memory read to the direct Crep
shared-memory operation and its post-state relation.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_shMemLoad_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (name : VarName) (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue oldValue : α)
      (slot : Nat),
      sharedMem (loadMemOp size) slot addressValue state = some targetState →
      sourceLocals name = some (.word oldValue) →
      panValueCrepStateRel structs context
        (updatePanValueMap sourceLocals name (.word valueValue)) sourceGlobals
        sourceMemory targetState) :
    PanValueCrepProgramCorrect
      (.shMemLoad size .local name address.toExp) := by
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
            (fun current value hvalue =>
              hlookup context sourceLocals current value hvalue)
            address addressValue' haddress
          have hsourceAddress :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord address.toExp =
                some (.word addressValue) := by
            rw [haddress, haddressWord]
          cases hmemory : sourceMemory addressValue with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                hsourceAddress, hmemory] at hsource
          | some memoryValue =>
              cases memoryValue with
              | word valueValue =>
                  have hmemoryWord :
                      sourceMemory addressValue = some (.word valueValue) := by
                    rw [hmemory]
                  have hsource' := hsource
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    hsourceAddress, hmemoryWord] at hsource'
                  have hlocal : ∃ oldValue,
                      sourceLocals name = some (.word oldValue) := by
                    cases hlocal : sourceLocals name with
                    | none =>
                        simp [panValueSharedLoadValid, panValueAssignmentValid,
                          hlocal] at hsource'
                    | some oldValue =>
                        cases oldValue with
                        | word oldValue =>
                            exact ⟨oldValue, by simp [hlocal]⟩
                        | rStruct fields =>
                            simp [panValueSharedLoadValid, panValueAssignmentValid,
                              hlocal,
                              panValueShape, panShapeMatches] at hsource'
                        | nStruct oldName fields =>
                            simp [panValueSharedLoadValid, panValueAssignmentValid,
                              hlocal,
                              panValueShape, panShapeMatches] at hsource'
                  obtain ⟨oldValue, hlocal⟩ := hlocal
                  have hsourceExpected :
                      evalPanValueProgWithPrimitiveCallsAndFfi
                        primitive sourceHandler structs sourceFunctions
                        baseAddress topAddress bytesInWord (sourceFuel + 1)
                        sourceLocals sourceGlobals sourceMemory
                        (.shMemLoad size .local name address.toExp) =
                      some (.normal
                        (updatePanValueMap sourceLocals name (.word valueValue))
                        sourceGlobals sourceMemory) := by
                    have hvalid :
                        panValueAssignmentValid structs sourceLocals sourceGlobals
                          .local name (.word valueValue) = true := by
                      simpa [panValueSharedLoadValid] using hsource'.1
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                      hsourceAddress, hmemoryWord, hvalid, hlocal,
                      panValueSharedLoadValid]
                  obtain ⟨slot, hslot⟩ :=
                    hlookup context sourceLocals name (.word oldValue) hlocal
                  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory state.locals state.memory
                      baseAddress topAddress bytesInWord
                      (hbytesInWord context bytesInWord) hrel.2.1
                      (fun current value hvalue =>
                        hlookup context sourceLocals current value hvalue)
                      address addressValue hsourceAddress
                  have hfirstAddress :
                      firstCompiledExp context address.toExp = some compiledAddress := by
                    simp [firstCompiledExp, hcompileAddress]
                  have hcompileProg :
                      compileProg context
                          (.shMemLoad size .local name address.toExp) =
                        .shMem (loadMemOp size) slot compiledAddress := by
                    simp [compileProg, hslot, hfirstAddress]
                  rw [hcompileProg] at hcrep
                  cases targetFuel with
                  | zero =>
                      simp [evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases hshared : sharedMem (loadMemOp size) slot
                          addressValue state with
                      | none =>
                          simp [evalCrepFullProg, hcrepAddress, hshared] at hcrep
                      | some targetState =>
                          have htargetRel := hsharedRel context structs
                            sourceLocals sourceGlobals sourceMemory state targetState
                            crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord addressValue valueValue oldValue slot
                            hshared hlocal
                          have hresult :=
                            compile_full_pan_value_shMemLoad_word_relation
                              context structs sourceFunctions functions sourceLocals
                              sourceGlobals sourceMemory state targetState primitive
                              sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord targetFuel
                              exceptionRel size name slot addressValue valueValue
                              oldValue address.toExp compiledAddress hslot
                              hsourceAddress hmemoryWord hfirstAddress hcrepAddress
                              hshared hlocal htargetRel
                          have hsourceEq :=
                            Option.some.inj (hsourceExpected.symm.trans hsource)
                          have hcrepForRelation :
                              evalCrepFullProg functions crepPrimitive ffi sharedMem
                                baseAddress topAddress (targetFuel + 1) state
                                (compileProg context
                                  (.shMemLoad size .local name address.toExp)) =
                                some crepResult := by
                            simpa [hcompileProg, Nat.add_assoc] using hcrep
                          have hcrepEq :=
                            Option.some.inj (hresult.2.1.symm.trans hcrepForRelation)
                          have hcontrol := hresult.2.2
                          rw [hsourceEq, hcrepEq] at hcontrol
                          exact hcontrol
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    hsourceAddress, hmemory, panValueSharedLoadValid] at hsource
              | nStruct structName fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    hsourceAddress, hmemory, panValueSharedLoadValid] at hsource

end Flapjack
