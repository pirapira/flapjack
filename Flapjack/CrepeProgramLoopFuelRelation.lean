import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeLoopCorrectness

/-!
Fuel-polymorphic zero-condition loop simulation.  This is the terminating
loop branch used by the compositional Pancake correctness induction.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_while_source_word_zero_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (condition : SourceWordExp α) (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition.toExp =
      some (.word sourceCondition))
    (hconditionAgreement : targetCondition = sourceCondition)
    (hzero : sourceCondition = 0)
    (hcompileBody : compileProg context body = compiledBody) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some (.normal sourceLocals sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) =
      some (.normal state) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal state) := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hrel.2.1 hlookup condition sourceCondition hsourceCondition
  have hsourceZero : sourceCondition = 0 := by
    simpa using hzero
  have htargetZero : targetCondition = 0 := by
    simpa [hconditionAgreement] using hsourceZero
  have hcompile : compileProg context (.while condition.toExp body) =
    .while compiledCondition compiledBody := by
    simp [compileProg, hcompileCondition, hcompileBody]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceZero]
  constructor
  · simp [evalCrepFullProg, hcrepCondition, hsourceZero, htargetZero]
  · exact hrel

end Flapjack
