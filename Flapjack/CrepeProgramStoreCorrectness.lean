import Flapjack.CrepeSourceWordStoreCorrectness
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word correctness for fixed-width stores.

Both operands are scalar source expressions, so the expression relation gives
the exact Crep expressions and their evaluations.  The store relation then
supplies the source/Crep memory update and control-result relation for any
positive target fuel.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_store32_source_word
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
    PanValueCrepProgramCorrect (.store32 address.toExp value.toExp) := by
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
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.store32 address.toExp value.toExp) =
                    some (.normal sourceLocals sourceGlobals
                      (updatePanValueMemory sourceMemory addressValue
                        (.word valueValue))) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  hsourceAddress, hsourceValue]
              cases targetFuel with
              | zero =>
                  simp [evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  have hresult := compile_full_pan_value_store32_relation
                    context structs sourceFunctions functions sourceLocals
                    sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress
                    bytesInWord targetFuel address.toExp value.toExp
                    compiledAddress compiledValue addressValue addressValue
                    valueValue valueValue hcompileAddress hcompileValue
                    hsourceAddress hsourceValue hcrepAddress hcrepValue rfl rfl hrel
                  have hsourceEq :=
                    Option.some.inj (hsourceExpected.symm.trans hsource)
                  have hcrepEq :=
                    Option.some.inj (hresult.2.1.symm.trans hcrep)
                  cases hsourceEq
                  cases hcrepEq
                  exact hresult.2.2

end Flapjack
