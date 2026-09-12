import Flapjack.CrepeProgramRaiseSourceWordRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word raise correctness.

The raise lowering evaluates a scalar expression in a fresh temporary, spills
it to global address zero, and then raises the compiled exception code.  The
exception lookup and relation assumptions are explicit because the compiler
has a skip fallback when either lookup fails.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_raise_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (value exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.word value) exceptionCode) :
    PanValueCrepProgramCorrect (.raise exception expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some sourceValue =>
          obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            expression sourceValue hvalue
          have hsourceValue :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord expression.toExp =
                some (.word value) := by
            rw [hvalue, hword]
          obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
          have hexception' := hexception context exceptionRel value exceptionCode
            hlookupCode
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWordExp_relation context structs sourceLocals sourceGlobals
              sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
              (hbytesInWord context bytesInWord) hrel.2.1
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              expression value hsourceValue
          cases targetFuel with
          | zero =>
              simp [compileProg, hlookupCode, hcompile, freshNames,
                nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProg] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [compileProg, hlookupCode, hcompile, freshNames,
                    nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [compileProg, hlookupCode, hcompile, freshNames,
                        nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [compileProg, hlookupCode, hcompile, freshNames,
                            nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProg] at hcrep
                      | succ targetFuel =>
                          have hresult :=
                            compile_full_pan_value_raise_source_word_relation_fuel
                              context structs sourceFunctions functions
                              sourceLocals sourceGlobals sourceMemory state
                              primitive sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord sourceFuel targetFuel
                              exception exceptionCode value expression compiled
                              exceptionRel hlookupCode
                              (hbytesInWord context bytesInWord) hrel hsourceValue
                              hcompile hcompiled hexception' 
                              (hfresh context state)
                          have hsourceEq :=
                            Option.some.inj (hresult.1.symm.trans hsource)
                          have hcrepEq :=
                            Option.some.inj (hresult.2.1.symm.trans hcrep)
                          cases hsourceEq
                          cases hcrepEq
                          exact ⟨0, hresult.2.2⟩

theorem panValueCrepProgramStateCorrect_raise_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (value exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.word value) exceptionCode) :
    PanValueCrepProgramStateCorrect (.raise exception expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some sourceValue =>
          obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            expression sourceValue hvalue
          have hsourceValue :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord expression.toExp =
                some (.word value) := by
            rw [hvalue, hword]
          obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
          have hexception' := hexception context exceptionRel value exceptionCode
            hlookupCode
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWordExp_relation context structs sourceLocals sourceGlobals
              sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
              (hbytesInWord context bytesInWord) hrel.2.1
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              expression value hsourceValue
          obtain ⟨compiled', hcompile', hnoGlobal⟩ :=
            compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              expression value hsourceValue
          have hcompiledEq : compiled = compiled' := by
            have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
              hcompile.symm.trans hcompile'
            exact (List.cons.inj (congrArg Prod.fst hpair)).1
          subst compiled'
          have hcompiledState :
              evalCrepFullExpState state baseAddress topAddress compiled =
                some value := by
            calc
              evalCrepFullExpState state baseAddress topAddress compiled =
                  evalCrepFullExp state.locals state.memory
                    baseAddress topAddress compiled :=
                evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
                  compiled hnoGlobal
              _ = some value := hcompiled
          cases targetFuel with
          | zero =>
              simp [compileProg, hlookupCode, hcompile, freshNames,
                nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [compileProg, hlookupCode, hcompile, freshNames,
                    nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [compileProg, hlookupCode, hcompile, freshNames,
                        nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [compileProg, hlookupCode, hcompile, freshNames,
                            nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          have hresult :=
                            compile_full_pan_value_raise_source_word_global_relation_fuel
                              context structs sourceFunctions functions
                              sourceLocals sourceGlobals sourceMemory state
                              primitive sourceHandler crepPrimitive ffi sharedMem
                              baseAddress topAddress bytesInWord sourceFuel targetFuel
                              exception exceptionCode value expression compiled
                              exceptionRel hlookupCode
                              (hbytesInWord context bytesInWord) hrel hsourceValue
                              hcompile hcompiledState hexception'
                              (hfresh context state)
                          have hsourceEq :=
                            Option.some.inj (hresult.1.symm.trans hsource)
                          have hcrepEq :=
                            Option.some.inj (hresult.2.1.symm.trans hcrep)
                          cases hsourceEq
                          cases hcrepEq
                          exact ⟨0, hresult.2.2.1.1, hresult.2.2.2⟩

end Flapjack
