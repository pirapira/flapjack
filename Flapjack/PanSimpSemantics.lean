import Flapjack.Pancake.PanSimp
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


/-!
Congruence helpers used to lift sequence-shape rewriting through the
recursive `dec`, `seq` and `ite` clauses, and the resulting full
`seqAssoc` preservation theorem (CakeML's `evaluate_seq_assoc`).
-/

abbrev SEval (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (program : Prog α) :=
  evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord locals globals
    memory primitive program (memoryAccess := memoryAccess)

theorem seq_congr_left (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (first first' second : Prog α)
    (h : SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory first
       = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory first') :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq first second)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq first' second) := by
  simp only [SEval, evalPanValueProgWithPrimitive]
  simp only [h]

theorem seq_congr_right (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (first second second' : Prog α)
    (h : ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory second
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory second') :
    ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.seq first second)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.seq first second') := by
  intro locals globals memory
  simp only [SEval, evalPanValueProgWithPrimitive]
  cases hfirst : evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
      locals globals memory primitive first (memoryAccess := memoryAccess) with
  | none => simp
  | some firstResult =>
      obtain ⟨fl, fg, fm, fv⟩ := firstResult
      cases fv with
      | nil => simpa [Option.bind_some] using h fl fg fm
      | cons value rest => simp

theorem dec_congr (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (name : VarName) (shape : Shape) (value : Exp α) (body body' : Prog α)
    (h : ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory body
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory body') :
    ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.dec name shape value body)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.dec name shape value body') := by
  intro locals globals memory
  simp only [SEval, evalPanValueProgWithPrimitive]
  cases hval : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => simp
  | some v =>
      simp
      by_cases hmatch : panShapeMatches (panValueShape structs v) shape = true
      · simp only [hmatch, if_true]
        simp only [h (updatePanValueMap locals name v) globals memory]
      · simp [hmatch]

theorem ite_congr (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (condition : Exp α) (thenBranch thenBranch' elseBranch elseBranch' : Prog α)
    (hthen : ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory thenBranch
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory thenBranch')
    (helse : ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory elseBranch
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory elseBranch') :
    ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.ite condition thenBranch elseBranch)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.ite condition thenBranch' elseBranch') := by
  intro locals globals memory
  simp only [SEval, evalPanValueProgWithPrimitive]
  cases hcond : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      condition (memoryAccess := memoryAccess) with
  | none => simp
  | some v =>
      simp
      cases v with
      | word w =>
          by_cases hz : (w != 0) = true
          · simp only [hz, if_true]
            exact hthen locals globals memory
          · simp [hz]
            exact helse locals globals memory
      | rStruct fields => simp
      | nStruct name fields => simp

theorem seq_annot (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α) (memoryAccess : Option (PanValueMemoryAccess α))
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (pre : Prog α) (tag text : String) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq pre (.annot tag text))
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory pre := by
  simp only [SEval, evalPanValueProgWithPrimitive]
  cases h : evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
      locals globals memory primitive pre (memoryAccess := memoryAccess) with
  | none => simp
  | some result =>
      obtain ⟨l, g, m, values⟩ := result
      cases values <;> simp

theorem seq_skipEval (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (primitive : PanPrimitiveHandler α) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq program (.skip : Prog α))
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory program :=
  evalPanValueProgWithPrimitive_seq_skip structs baseAddress topAddress bytesInWord locals globals
    memory primitive program memoryAccess

theorem skip_seqEval (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (primitive : PanPrimitiveHandler α) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq (.skip : Prog α) program)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory program :=
  evalPanValueProgWithPrimitive_skip_seq structs baseAddress topAddress bytesInWord locals globals
    memory primitive program memoryAccess

theorem smartSeqEval (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (primitive : PanPrimitiveHandler α) (pre program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (smartSeq pre program)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq pre program) :=
  evalPanValueProgWithPrimitive_smartSeq structs baseAddress topAddress bytesInWord locals globals
    memory primitive pre program memoryAccess

theorem seq_assocEval (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (primitive : PanPrimitiveHandler α) (first second third : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq (.seq first second) third)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (.seq first (.seq second third)) :=
  evalPanValueProgWithPrimitive_seq_assoc structs baseAddress topAddress bytesInWord locals globals
    memory primitive first second third memoryAccess

theorem evalPanValueProgWithPrimitive_seqAssoc (structs : StructContext)
    (baseAddress topAddress bytesInWord : α) (primitive : PanPrimitiveHandler α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    ∀ (program pre : Prog α) (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (seqAssoc pre program)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (.seq pre program) := by
  intro program pre locals globals memory
  have main : ∀ n, ∀ (program : Prog α), sizeOf program = n →
      ∀ (pre : Prog α) (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
            memory (seqAssoc pre program)
          = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
            memory (.seq pre program) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hsize pre locals globals memory
      cases program with
      | skip =>
          rw [seqAssoc.eq_1]
          exact (seq_skipEval structs baseAddress topAddress bytesInWord locals globals memory
            primitive pre memoryAccess).symm
      | dec name shape value body =>
          rw [seqAssoc.eq_2, smartSeqEval]
          apply seq_congr_right
          intro l g m
          apply dec_congr
          intro ll gg mm
          rw [ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl .skip ll gg mm]
          exact skip_seqEval structs baseAddress topAddress bytesInWord ll gg mm primitive body
            memoryAccess
      | seq first second =>
          rw [seqAssoc.eq_3]
          rw [ih (sizeOf second) (by rw [← hsize]; decreasing_trivial) second rfl
            (seqAssoc pre first) locals globals memory]
          rw [seq_congr_left structs baseAddress topAddress bytesInWord primitive memoryAccess
            locals globals memory (seqAssoc pre first) (.seq pre first) second
            (ih (sizeOf first) (by rw [← hsize]; decreasing_trivial) first rfl pre
              locals globals memory)]
          exact seq_assocEval structs baseAddress topAddress bytesInWord locals globals memory
            primitive pre first second memoryAccess
      | ite condition thenBranch elseBranch =>
          rw [seqAssoc.eq_4, smartSeqEval]
          apply seq_congr_right
          intro l g m
          apply ite_congr
          · intro ll gg mm
            rw [ih (sizeOf thenBranch) (by rw [← hsize]; decreasing_trivial) thenBranch rfl
              .skip ll gg mm]
            exact skip_seqEval structs baseAddress topAddress bytesInWord ll gg mm primitive
              thenBranch memoryAccess
          · intro ll gg mm
            rw [ih (sizeOf elseBranch) (by rw [← hsize]; decreasing_trivial) elseBranch rfl
              .skip ll gg mm]
            exact skip_seqEval structs baseAddress topAddress bytesInWord ll gg mm primitive
              elseBranch memoryAccess
      | «while» condition body =>
          rw [seqAssoc.eq_5, smartSeqEval]
          apply seq_congr_right
          intro l g m
          simp only [SEval, evalPanValueProgWithPrimitive]
      | call info function arguments =>
          cases info with
          | none => rw [seqAssoc.eq_6, smartSeqEval]
          | some info =>
              obtain ⟨returns, handlerInfo⟩ := info
              cases handlerInfo with
              | none => rw [seqAssoc.eq_7, smartSeqEval]
              | some handlerInfo =>
                  obtain ⟨exception, handlerVar, handler⟩ := handlerInfo
                  rw [seqAssoc.eq_8, smartSeqEval]
                  apply seq_congr_right
                  intro l g m
                  simp only [SEval, evalPanValueProgWithPrimitive]
      | decCall name shape function arguments body =>
          rw [seqAssoc.eq_9, smartSeqEval]
          apply seq_congr_right
          intro l g m
          simp only [SEval, evalPanValueProgWithPrimitive]
      | annot tag text =>
          rw [show seqAssoc pre (.annot tag text) = pre from by simp [seqAssoc]]
          exact (seq_annot structs baseAddress topAddress bytesInWord primitive memoryAccess
            locals globals memory pre tag text).symm
      | assign kind name value => simp [seqAssoc, smartSeqEval]
      | primitive name operator arguments => simp [seqAssoc, smartSeqEval]
      | store address value => simp [seqAssoc, smartSeqEval]
      | store32 address value => simp [seqAssoc, smartSeqEval]
      | storeByte address value => simp [seqAssoc, smartSeqEval]
      | «break» => simp [seqAssoc, smartSeqEval]
      | «continue» => simp [seqAssoc, smartSeqEval]
      | extCall function configuration configurationLength array arrayLength =>
          simp [seqAssoc, smartSeqEval]
      | «raise» exception value => simp [seqAssoc, smartSeqEval]
      | «return» value => simp [seqAssoc, smartSeqEval]
      | shMemLoad size kind name address => simp [seqAssoc, smartSeqEval]
      | shMemStore size address value => simp [seqAssoc, smartSeqEval]
      | tick => simp [seqAssoc, smartSeqEval]
  exact main (sizeOf program) program rfl pre locals globals memory

/-- CakeML's `eval_seq_assoc_eq_evaluate` / `eval_seq_assoc_not_error`:
    `seq_assoc Skip` is semantics-preserving, so a successful evaluation of
    the original program is exactly a successful evaluation of the
    sequence-associated program. -/
theorem evalPanValueProgWithPrimitive_seqAssoc_skip (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (seqAssoc (.skip : Prog α) program)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory program := by
  rw [evalPanValueProgWithPrimitive_seqAssoc]
  exact skip_seqEval structs baseAddress topAddress bytesInWord locals globals memory
    primitive program memoryAccess

/-- CakeML's `evaluate_seq_no_error_fst`: a successful evaluation of
    `Seq first second` exposes a successful evaluation of `first`. -/
theorem evalPanValueProgWithPrimitive_seq_some_fst (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (first second : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
    (result : (VarName → Option (PanValue α)) × (VarName → Option (PanValue α))
      × (α → Option (PanValue α)) × List (PanValue α)) :
    evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive (.seq first second)
        (memoryAccess := memoryAccess) = some result →
    ∃ firstResult, evalPanValueProgWithPrimitive structs baseAddress topAddress
        bytesInWord locals globals memory primitive first
        (memoryAccess := memoryAccess) = some firstResult := by
  intro h
  cases hfirst : evalPanValueProgWithPrimitive structs baseAddress topAddress
      bytesInWord locals globals memory primitive first
      (memoryAccess := memoryAccess) with
  | none => simp [evalPanValueProgWithPrimitive, hfirst] at h
  | some firstResult => exact ⟨firstResult, rfl⟩

/-- CakeML's tail-call recognition is evaluation-preserving: the
    `seqCallRet` rewrite of an `AssignCall`/`Return` shape does not change
    the structured evaluation. -/
theorem evalPanValueProgWithPrimitive_seqCallRet (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory (seqCallRet program)
      = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
        memory program := by
  unfold seqCallRet
  split
  · split <;> simp [SEval, evalPanValueProgWithPrimitive]
  · rfl

/-- CakeML's `ret_to_tail_correct` on the structured evaluator: the
    `pan_simp` tail-call rewrite preserves evaluation. -/
theorem evalPanValueProgWithPrimitive_retToTail (structs : StructContext)
    (baseAddress topAddress bytesInWord : α) (primitive : PanPrimitiveHandler α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    ∀ (program : Prog α) (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory (retToTail program)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
          memory program := by
  intro program locals globals memory
  have main : ∀ n, ∀ (program : Prog α), sizeOf program = n →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)),
        SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
            memory (retToTail program)
          = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess locals globals
            memory program := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hsize locals globals memory
      cases program with
      | skip =>
          rw [retToTail.eq_1]
      | dec name shape value body =>
          rw [retToTail.eq_2]
          exact dec_congr structs baseAddress topAddress bytesInWord primitive memoryAccess
            name shape value (retToTail body) body
            (fun l g m => ih (sizeOf body) (by rw [← hsize]; decreasing_trivial)
              body rfl l g m)
            locals globals memory
      | seq first second =>
          rw [retToTail.eq_3]
          calc
            SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
                locals globals memory
                (seqCallRet (.seq (retToTail first) (retToTail second)))
              = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
                  locals globals memory (.seq (retToTail first) (retToTail second)) :=
                evalPanValueProgWithPrimitive_seqCallRet structs baseAddress topAddress
                  bytesInWord locals globals memory primitive
                  (.seq (retToTail first) (retToTail second)) memoryAccess
            _ = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
                  locals globals memory (.seq first (retToTail second)) :=
                seq_congr_left structs baseAddress topAddress bytesInWord primitive
                  memoryAccess locals globals memory (retToTail first) first
                  (retToTail second)
                  (ih (sizeOf first) (by rw [← hsize]; decreasing_trivial)
                    first rfl locals globals memory)
            _ = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
                  locals globals memory (.seq first second) :=
                seq_congr_right structs baseAddress topAddress bytesInWord primitive
                  memoryAccess first (retToTail second) second
                  (fun l g m => ih (sizeOf second) (by rw [← hsize]; decreasing_trivial)
                    second rfl l g m)
                  locals globals memory
      | ite condition thenBranch elseBranch =>
          rw [retToTail.eq_4]
          exact ite_congr structs baseAddress topAddress bytesInWord primitive memoryAccess
            condition (retToTail thenBranch) thenBranch (retToTail elseBranch) elseBranch
            (fun l g m => ih (sizeOf thenBranch) (by rw [← hsize]; decreasing_trivial)
              thenBranch rfl l g m)
            (fun l g m => ih (sizeOf elseBranch) (by rw [← hsize]; decreasing_trivial)
              elseBranch rfl l g m)
            locals globals memory
      | «while» condition body =>
          rw [retToTail.eq_5]
          simp [SEval, evalPanValueProgWithPrimitive]
      | «call» info function arguments =>
          cases info with
          | none =>
              rw [retToTail.eq_6]
          | some info =>
              cases info with
              | mk returns handlerInfo =>
                  cases handlerInfo with
                  | none =>
                      rw [retToTail.eq_7]
                  | some handler =>
                      cases handler with
                      | mk exception handlerInfo =>
                          cases handlerInfo with
                          | mk handlerVar handlerProgram =>
                              rw [retToTail.eq_8]
                              simp [SEval, evalPanValueProgWithPrimitive]
      | decCall name shape function arguments body =>
          rw [retToTail.eq_9]
          simp [SEval, evalPanValueProgWithPrimitive]
      | annot tag text =>
          simp [retToTail]
      | assign kind name value => simp [retToTail]
      | primitive name operator arguments => simp [retToTail]
      | store address value => simp [retToTail]
      | store32 address value => simp [retToTail]
      | storeByte address value => simp [retToTail]
      | «break» => simp [retToTail]
      | «continue» => simp [retToTail]
      | extCall function configuration configurationLength array arrayLength =>
          simp [retToTail]
      | «raise» exception value => simp [retToTail]
      | «return» value => simp [retToTail]
      | shMemLoad size kind name address => simp [retToTail]
      | shMemStore size address value => simp [retToTail]
      | tick => simp [retToTail]
  exact main (sizeOf program) program rfl locals globals memory

/-- CakeML's `compile_correct_same_state` / `evaluate_seq_simp` on the
    structured fragment: running the whole `pan_simp` transformation
    (`panSimpProg = retToTail (seqAssoc Skip ·)`) preserves evaluation. -/
theorem evalPanValueProgWithPrimitive_panSimpProg (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (primitive : PanPrimitiveHandler α)
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    ∀ (program : Prog α) (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)),
      SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
          locals globals memory (panSimpProg program)
        = SEval structs baseAddress topAddress bytesInWord primitive memoryAccess
          locals globals memory program := by
  intro program locals globals memory
  simp only [panSimpProg]
  rw [evalPanValueProgWithPrimitive_retToTail structs baseAddress topAddress
    bytesInWord primitive memoryAccess (seqAssoc (.skip : Prog α) program)
    locals globals memory]
  exact evalPanValueProgWithPrimitive_seqAssoc_skip structs baseAddress topAddress
    bytesInWord locals globals memory primitive program memoryAccess

end Flapjack
