import Flapjack.PanSimp
import Flapjack.PanValues

/-!
Evaluator-level correctness of the `pan_simp` sequence-shape helper
(`smartSeq`, `seqAssoc`, `retToTail`) on the clock-free structured-value
evaluator.

These are the Lean counterparts of CakeML's `pan_simpProofScript.sml`
`evaluate_seq_skip`, `evaluate_skip_seq`, `evaluate_SmartSeq`, and the
sequence-associativity step used by `evaluate_seq_assoc`.
-/

namespace Flapjack

variable {α : Type} [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
  [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
  [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]

/-- CakeML's `evaluate_seq_skip`: appending `Skip` to a program does not
    change its evaluation. -/
theorem evalPanValueProgWithPrimitive_seq_skip (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq program (.skip : Prog α))
        (memoryAccess := memoryAccess)
      = evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive program (memoryAccess := memoryAccess) := by
  simp only [evalPanValueProgWithPrimitive]
  cases h : evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
      locals globals memory primitive program (memoryAccess := memoryAccess) with
  | none => simp
  | some result =>
      obtain ⟨l, g, m, values⟩ := result
      cases values <;> simp

/-- CakeML's `evaluate_skip_seq`: prefixing `Skip` to a program does not
    change its evaluation. -/
theorem evalPanValueProgWithPrimitive_skip_seq (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq (.skip : Prog α) program)
        (memoryAccess := memoryAccess)
      = evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive program (memoryAccess := memoryAccess) := by
  simp [evalPanValueProgWithPrimitive]

/-- CakeML's `evaluate_SmartSeq`: `SmartSeq p q` evaluates exactly like
    `Seq p q`. -/
theorem evalPanValueProgWithPrimitive_smartSeq (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (pre program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (smartSeq pre program)
        (memoryAccess := memoryAccess)
      = evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq pre program)
        (memoryAccess := memoryAccess) := by
  cases pre <;> simp only [smartSeq]
  · exact (evalPanValueProgWithPrimitive_skip_seq structs baseAddress topAddress
      bytesInWord locals globals memory primitive program memoryAccess).symm
  all_goals rfl

/-- Sequence associativity of the evaluator: `Seq (Seq p q) r` and
    `Seq p (Seq q r)` have the same evaluation.  This is the semantic
    ingredient behind CakeML's `evaluate_seq_assoc`. -/
theorem evalPanValueProgWithPrimitive_seq_assoc (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (first second third : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq (.seq first second) third)
        (memoryAccess := memoryAccess)
      = evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq first (.seq second third))
        (memoryAccess := memoryAccess) := by
  simp only [evalPanValueProgWithPrimitive]
  cases hfirst : evalPanValueProgWithPrimitive structs baseAddress topAddress
      bytesInWord locals globals memory primitive first
      (memoryAccess := memoryAccess) with
  | none => simp
  | some firstResult =>
      obtain ⟨fl, fg, fm, firstValues⟩ := firstResult
      cases firstValues with
      | cons value rest => simp
      | nil =>
          cases hsecond : evalPanValueProgWithPrimitive structs baseAddress
              topAddress bytesInWord fl fg fm primitive second
              (memoryAccess := memoryAccess) with
          | none => simp [hsecond]
          | some secondResult =>
              obtain ⟨sl, sg, sm, secondValues⟩ := secondResult
              cases secondValues <;> simp [hsecond]

end Flapjack