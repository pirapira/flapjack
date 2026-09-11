import Flapjack.CrepeStateRelation

/-!
Base cases for the source-to-Crep program simulation.

These constructors do not inspect handlers, function tables, or memory.  The
theorem packages their exact source and target results together with the state
relation so that the main correctness induction can use them without
unfolding either evaluator.
-/

namespace Flapjack

theorem compile_full_pan_value_basic_control_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (program : Prog α)
    (hprogram : program = .skip ∨ program = .break ∨ program = .continue ∨
      program = .tick ∨ ∃ tag text, program = .annot tag text)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    ∃ sourceResult crepResult,
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord (fuel + 1)
        sourceLocals sourceGlobals sourceMemory program = some sourceResult ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context program) = some crepResult ∧
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  rcases hprogram with rfl | rfl | rfl | rfl | ⟨tag, text, rfl⟩
  · exact ⟨.normal sourceLocals sourceGlobals sourceMemory, .normal state,
      by simp [evalPanValueProgWithPrimitiveCallsAndFfi],
      by simp [compileProg, evalCrepFullProg], hrel⟩
  · exact ⟨.broke sourceLocals sourceGlobals sourceMemory, .broke state 0,
      by simp [evalPanValueProgWithPrimitiveCallsAndFfi],
      by simp [compileProg, evalCrepFullProg], by simpa [panValueCrepControlRel] using hrel⟩
  · exact ⟨.continued sourceLocals sourceGlobals sourceMemory, .continued state 0,
      by simp [evalPanValueProgWithPrimitiveCallsAndFfi],
      by simp [compileProg, evalCrepFullProg], by simpa [panValueCrepControlRel] using hrel⟩
  · exact ⟨.normal sourceLocals sourceGlobals sourceMemory, .normal state,
      by simp [evalPanValueProgWithPrimitiveCallsAndFfi],
      by simp [compileProg, evalCrepFullProg], hrel⟩
  · exact ⟨.normal sourceLocals sourceGlobals sourceMemory, .normal state,
      by simp [evalPanValueProgWithPrimitiveCallsAndFfi],
      by simp [compileProg, evalCrepFullProg], hrel⟩

end Flapjack
