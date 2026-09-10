import Flapjack.CrepeStateRelation

/-!
Relation-aware short-circuiting for non-normal sequence results.

The source and Crep evaluators both return a non-normal first result without
evaluating the second program.  This is the control-propagation case needed by
the program correctness induction.
-/

namespace Flapjack

theorem compile_full_pan_value_seq_control_relation
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
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some sourceResult)
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some crepResult)
    (hsourceNonNormal : ∀ locals globals memory,
      sourceResult ≠ .normal locals globals memory)
    (hcrepNonNormal : ∀ state,
      crepResult ≠ .normal state)
    (hrel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some crepResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult := by
  constructor
  · cases hsourceResult : sourceResult with
    | normal locals globals memory =>
        exact False.elim (hsourceNonNormal locals globals memory hsourceResult)
    | returned locals globals memory values =>
        rw [hsourceResult] at hsourceFirst
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
    | raised locals globals memory exception value =>
        rw [hsourceResult] at hsourceFirst
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
    | broke locals globals memory =>
        rw [hsourceResult] at hsourceFirst
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
    | continued locals globals memory =>
        rw [hsourceResult] at hsourceFirst
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst]
  constructor
  · cases hcrepResult : crepResult with
    | normal state =>
        exact False.elim (hcrepNonNormal state hcrepResult)
    | returned state values =>
        rw [hcrepResult] at hcrepFirst
        simp [compileProg, hcompileFirst, hcompileSecond,
          evalCrepFullProg, hcrepFirst]
    | raised state exception =>
        rw [hcrepResult] at hcrepFirst
        simp [compileProg, hcompileFirst, hcompileSecond,
          evalCrepFullProg, hcrepFirst]
    | broke state label =>
        rw [hcrepResult] at hcrepFirst
        simp [compileProg, hcompileFirst, hcompileSecond,
          evalCrepFullProg, hcrepFirst]
    | continued state label =>
        rw [hcrepResult] at hcrepFirst
        simp [compileProg, hcompileFirst, hcompileSecond,
          evalCrepFullProg, hcrepFirst]
    | finalFfi state event =>
        rw [hcrepResult] at hcrepFirst
        simp [compileProg, hcompileFirst, hcompileSecond,
          evalCrepFullProg, hcrepFirst]
  · exact hrel

end Flapjack
