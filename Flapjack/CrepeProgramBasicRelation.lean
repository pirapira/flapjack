import Flapjack.CrepeProgramRelation

/-!
Basic cases for the compositional source-to-Crep program relation.

These constructors do not evaluate expressions or consult handlers.  Keeping
them in the program-relation API makes the first cases of the Pancake
correctness induction independent of evaluator implementation details.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_basic_control
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (hprogram : program = .skip ∨ program = .break ∨
      program = .continue ∨ program = .tick ∨
      ∃ tag text, program = .annot tag text) :
    PanValueCrepProgramCorrect program := by
  rcases hprogram with rfl | rfl | rfl | rfl | ⟨tag, text, rfl⟩
  all_goals
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
            simp [evalPanValueProgWithPrimitiveCallsAndFfi,
              evalCrepFullProg, compileProg] at hsource hcrep
            cases sourceResult <;> cases crepResult <;>
              simp_all [panValueCrepControlRel]

theorem panValueCrepProgramStateCorrect_basic_control
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (hprogram : program = .skip ∨ program = .break ∨
      program = .continue ∨ program = .tick ∨
      ∃ tag text, program = .annot tag text) :
    PanValueCrepProgramStateCorrect program := by
  rcases hprogram with rfl | rfl | rfl | rfl | ⟨tag, text, rfl⟩
  all_goals
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
            simp [evalPanValueProgWithPrimitiveCallsAndFfi,
              evalCrepFullProgState, compileProg] at hsource hcrep
            cases sourceResult <;> cases crepResult <;>
              simp_all [panValueCrepControlRel]

end Flapjack
