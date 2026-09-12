import Flapjack.CrepeSourceWordStoreCorrectness
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word correctness for byte stores.

At the word-memory abstraction used by the Pancake/Crep relation, the
StoreByte boundary has the same scalar expression and memory-update shape as
Store32.  The byte-specific source and Crep evaluator details remain inside
the reusable StoreByte relation.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_storeByte_source_word
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
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.storeByte address.toExp value.toExp) := by
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
                    (.storeByte address.toExp value.toExp) =
                    some (.normal sourceLocals sourceGlobals
                      (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue))) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  hsourceAddress, hsourceValue]
              cases targetFuel with
              | zero =>
                  simp [evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  have hresult := compile_full_pan_value_storeByte_source_word_relation
                    context structs sourceFunctions functions sourceLocals
                    sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress
                    bytesInWord targetFuel address value addressValue valueValue
                    (hbytesInWord context bytesInWord) hrel
                    (fun name value hvalue =>
                      hlookup context sourceLocals name value hvalue)
                    hsourceAddress hsourceValue
                  rcases hresult.2 with
                    ⟨compiledAddress, compiledValue, hcompileAddress,
                      hcompileValue, hcrepExpected, hrelation⟩
                  have hsourceEq :=
                    Option.some.inj (hsourceExpected.symm.trans hsource)
                  have hcrepEq :=
                    Option.some.inj (hcrepExpected.symm.trans hcrep)
                  cases hsourceEq
                  cases hcrepEq
                  exact hrelation

theorem panValueCrepProgramStateCorrect_storeByte_source_word
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
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.storeByte address.toExp value.toExp) := by
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
                    (.storeByte address.toExp value.toExp) =
                    some (.normal sourceLocals sourceGlobals
                      (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue))) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  hsourceAddress, hsourceValue]
              cases targetFuel with
              | zero =>
                  simp [evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  obtain ⟨_, ⟨compiledAddress, compiledValue,
                    hcompileAddress, hcompileValue, hcrepExpected, hrelation⟩⟩ :=
                    compile_full_pan_value_storeByte_source_word_state_relation
                      context structs sourceFunctions functions sourceLocals
                      sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress
                      bytesInWord targetFuel address value addressValue valueValue
                      (hbytesInWord context bytesInWord) hrel
                      (fun name value hvalue =>
                        hlookup context sourceLocals name value hvalue)
                      hsourceAddress hsourceValue
                  have hsourceEq :=
                    Option.some.inj (hsourceExpected.symm.trans hsource)
                  have hcrepEq :=
                    Option.some.inj (hcrepExpected.symm.trans hcrep)
                  cases hsourceEq
                  cases hcrepEq
                  exact hrelation

end Flapjack
