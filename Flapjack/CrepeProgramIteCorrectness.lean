import Flapjack.CrepeProgramRelation
import Flapjack.CrepeProgramConditionalFuelRelation

/-!
The conditional constructor of the compositional program correctness
predicate.  A positive-fuel helper handles source-word branch selection; the
constructor then discharges the zero-fuel cases required by the predicate's
arbitrary-fuel quantifiers.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_ite_source_word_pos
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthen : PanValueCrepProgramCorrect thenBranch)
    (helse : PanValueCrepProgramCorrect elseBranch)
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
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceResult)
    (hcrep : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepResult)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition.toExp with
  | none =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
        hcondition] at hsource
  | some conditionValue =>
      cases conditionValue with
      | word sourceCondition =>
          obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
            compileSourceWordExp_relation context structs sourceLocals sourceGlobals
              sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
              hbytesInWord hrel.2.1 hlookup condition sourceCondition hcondition
          have hcompile : compileProg context
              (.ite condition.toExp thenBranch elseBranch) =
              .ite compiledCondition (compileProg context thenBranch)
                (compileProg context elseBranch) := by
            simp [compileProg, hcompileCondition]
          rw [hcompile] at hcrep
          by_cases hnonzero : sourceCondition ≠ 0
          · have hsourceThen :
                evalPanValueProgWithPrimitiveCallsAndFfi
                  primitive sourceHandler structs sourceFunctions
                  baseAddress topAddress bytesInWord sourceFuel
                  sourceLocals sourceGlobals sourceMemory thenBranch =
                  some sourceResult := by
              simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, hcondition, hnonzero] using hsource
            have hcrepThen :
                evalCrepFullProg functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state
                  (compileProg context thenBranch) = some crepResult := by
              simpa [evalCrepFullProg, hcrepCondition, hnonzero] using hcrep
            have hthenRel := hthen context structs sourceFunctions functions
              sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
              crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
              sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
              hsourceThen hcrepThen
            exact (compile_full_pan_value_ite_source_word_then_relation_fuel
              context structs sourceFunctions functions sourceLocals sourceGlobals
              sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
              baseAddress topAddress bytesInWord sourceFuel targetFuel condition
              thenBranch elseBranch (compileProg context thenBranch)
              (compileProg context elseBranch) sourceCondition sourceCondition
              sourceResult crepResult exceptionRel hbytesInWord hrel hlookup
              hcondition rfl hnonzero rfl rfl hsourceThen hcrepThen hthenRel).2.2
          · have hzero : sourceCondition = 0 := by
              exact Classical.byContradiction (fun hnot => hnonzero hnot)
            have hsourceElse :
                evalPanValueProgWithPrimitiveCallsAndFfi
                  primitive sourceHandler structs sourceFunctions
                  baseAddress topAddress bytesInWord sourceFuel
                  sourceLocals sourceGlobals sourceMemory elseBranch =
                  some sourceResult := by
              simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, hcondition, hnonzero] using hsource
            have hcrepElse :
                evalCrepFullProg functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state
                  (compileProg context elseBranch) = some crepResult := by
              simpa [evalCrepFullProg, hcrepCondition, hnonzero] using hcrep
            have helseRel := helse context structs sourceFunctions functions
              sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
              crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
              sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
              hsourceElse hcrepElse
            exact (compile_full_pan_value_ite_source_word_else_relation_fuel
              context structs sourceFunctions functions sourceLocals sourceGlobals
              sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
              baseAddress topAddress bytesInWord sourceFuel targetFuel condition
              thenBranch elseBranch (compileProg context thenBranch)
              (compileProg context elseBranch) sourceCondition sourceCondition
              sourceResult crepResult exceptionRel hbytesInWord hrel hlookup
              hcondition rfl hzero rfl rfl hsourceElse hcrepElse helseRel).2.2
      | rStruct fields =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            hcondition] at hsource
      | nStruct name fields =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            hcondition] at hsource

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthen : PanValueCrepProgramCorrect thenBranch)
    (helse : PanValueCrepProgramCorrect elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect
      (.ite condition.toExp thenBranch elseBranch) := by
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
          exact panValueCrepProgramCorrect_ite_source_word_pos condition
            thenBranch elseBranch hthen helse context structs sourceFunctions
            functions sourceLocals sourceGlobals sourceMemory state primitive
            sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
            bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
            hrel hsource hcrep (hbytesInWord context bytesInWord)
            (hlookup context sourceLocals)

theorem panValueCrepProgramStateCorrect_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthen : PanValueCrepProgramStateCorrect thenBranch)
    (helse : PanValueCrepProgramStateCorrect elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
      (.ite condition.toExp thenBranch elseBranch) := by
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
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord condition.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource
          | some conditionValue =>
              cases conditionValue with
              | word sourceCondition =>
                  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory state.locals state.memory
                      baseAddress topAddress bytesInWord
                      (hbytesInWord context bytesInWord)
                      hrel.2.1 (hlookup context sourceLocals) condition
                      sourceCondition hcondition
                  have hcompile : compileProg context
                      (.ite condition.toExp thenBranch elseBranch) =
                      .ite compiledCondition (compileProg context thenBranch)
                        (compileProg context elseBranch) := by
                    simp [compileProg, hcompileCondition]
                  have hcrepConditionState :
                      evalCrepFullExpState state baseAddress topAddress
                        compiledCondition = some sourceCondition := by
                    obtain ⟨compiledCondition', hcompileCondition', hnoGlobal⟩ :=
                      compileSourceWordExp_noGlobal context structs sourceLocals
                        sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                        (hlookup context sourceLocals) condition sourceCondition
                        hcondition
                    have hcompiledEq : compiledCondition = compiledCondition' := by
                      have hpair : ([compiledCondition], Shape.one) =
                          ([compiledCondition'], Shape.one) :=
                        hcompileCondition.symm.trans hcompileCondition'
                      exact (List.cons.inj (congrArg Prod.fst hpair)).1
                    have hcrepCondition' :
                        evalCrepFullExp state.locals state.memory
                          baseAddress topAddress compiledCondition' =
                          some sourceCondition := by
                      simpa [hcompiledEq] using hcrepCondition
                    rw [hcompiledEq]
                    rw [evalCrepFullExpState_eq_of_noGlobal state
                      baseAddress topAddress compiledCondition' hnoGlobal]
                    exact hcrepCondition'
                  rw [hcompile] at hcrep
                  by_cases hnonzero : sourceCondition ≠ 0
                  · have hsourceThen :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory thenBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepThen :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context thenBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    have hthenRel := hthen context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceThen hcrepThen
                    exact (compile_full_pan_value_ite_source_word_then_state_relation_fuel
                      context structs sourceFunctions functions sourceLocals sourceGlobals
                      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                      baseAddress topAddress bytesInWord sourceFuel targetFuel condition
                      thenBranch elseBranch (compileProg context thenBranch)
                      (compileProg context elseBranch) sourceCondition sourceCondition
                      sourceResult crepResult exceptionRel
                      (hbytesInWord context bytesInWord) hrel
                      (hlookup context sourceLocals) hcondition rfl hnonzero rfl rfl
                      hsourceThen hcrepThen hthenRel).2.2
                  · have hzero : sourceCondition = 0 := by
                      exact Classical.byContradiction (fun hnot => hnonzero hnot)
                    have hsourceElse :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory elseBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepElse :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context elseBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    have helseRel := helse context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceElse hcrepElse
                    exact (compile_full_pan_value_ite_source_word_else_state_relation_fuel
                      context structs sourceFunctions functions sourceLocals sourceGlobals
                      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                      baseAddress topAddress bytesInWord sourceFuel targetFuel condition
                      thenBranch elseBranch (compileProg context thenBranch)
                      (compileProg context elseBranch) sourceCondition sourceCondition
                      sourceResult crepResult exceptionRel
                      (hbytesInWord context bytesInWord) hrel
                      (hlookup context sourceLocals) hcondition rfl hzero rfl rfl
                      hsourceElse hcrepElse helseRel).2.2
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    hcondition] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    hcondition] at hsource

end Flapjack
