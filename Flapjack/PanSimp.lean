import Flapjack.Language

/-!
The `pan_simp` pass from CakeML's Pancake development.

The pass associates sequences to the right while preserving declarations,
branches, loops, calls, and call handlers. It also recognizes the
`AssignCall`/`Return` shape as a tail call. In Pancake, `TailCall` is an
abbreviation for a call with no return information, so no extra AST
constructor is needed here.
-/

namespace Flapjack

def smartSeq : Prog α → Prog α → Prog α
  | .skip, program => program
  | pre, program => .seq pre program

def seqCallRet : Prog α → Prog α
  | .seq
      (.call (some (some (.local, returnName), none)) function arguments)
      (.return (.var .local returnedName)) =>
      if returnName = returnedName then
        .call none function arguments
      else
        .seq
          (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnedName))
  | program => program

def seqAssoc (pre : Prog α) : Prog α → Prog α
  | .skip => pre
  | .dec name shape value body =>
      smartSeq pre (.dec name shape value (seqAssoc .skip body))
  | .seq first second => seqAssoc (seqAssoc pre first) second
  | .ite condition thenBranch elseBranch =>
      smartSeq pre (.ite condition (seqAssoc .skip thenBranch)
        (seqAssoc .skip elseBranch))
  | .while condition body =>
      smartSeq pre (.while condition (seqAssoc .skip body))
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, seqAssoc .skip handler))
      smartSeq pre (.call info function arguments)
  | .decCall name shape function arguments body =>
      smartSeq pre (.decCall name shape function arguments (seqAssoc .skip body))
  | .annot _ _ => pre
  | program => smartSeq pre program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def retToTail : Prog α → Prog α
  | .skip => .skip
  | .dec name shape value body => .dec name shape value (retToTail body)
  | .seq first second =>
      seqCallRet (.seq (retToTail first) (retToTail second))
  | .ite condition thenBranch elseBranch =>
      .ite condition (retToTail thenBranch) (retToTail elseBranch)
  | .while condition body => .while condition (retToTail body)
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, retToTail handler))
      .call info function arguments
  | .decCall name shape function arguments body =>
      .decCall name shape function arguments (retToTail body)
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def panSimpProg (program : Prog α) : Prog α :=
  retToTail (seqAssoc .skip program)

def panSimpDecls : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := panSimpProg declaration.body } ::
        panSimpDecls declarations
  | declaration :: declarations => declaration :: panSimpDecls declarations
termination_by declarations => sizeOf declarations

@[simp] theorem smartSeq_skip (program : Prog α) :
    smartSeq (.skip : Prog α) program = program := by
  cases program <;> rfl

theorem panSimpProg_skip : panSimpProg (.skip : Prog α) = .skip := by
  simp [panSimpProg, seqAssoc, retToTail]

/-! `pan_simp` preserves the exception identifiers collected by the source
    program. These are the two local preservation steps used by Cake's
    `exp_ids_ret_to_tail_eq` and `exp_ids_seq_assoc_eq` proofs. -/

theorem expIds_seqCallRet (program : Prog α) :
    expIds (seqCallRet program) = expIds program := by
  unfold seqCallRet
  split
  · split <;> simp [expIds]
  · rfl

theorem expIds_smartSeq (pre program : Prog α) :
    expIds (smartSeq pre program) = expIds pre ++ expIds program := by
  cases pre <;> simp [smartSeq, expIds]

/-- `seq_assoc` preserves the exception identifiers collected by the source
    program (Cake's `exp_ids_seq_assoc_eq`).  The pass only recurses on the
    second argument, but the handler of a call is nested inside an `Option`,
    so the Lean definition is well-founded; we therefore run a strong
    induction on `sizeOf program` rather than the (ill-formed) unary
    induction principle. -/
theorem expIds_seqAssoc (program pre : Prog α) :
    expIds (seqAssoc pre program) = expIds pre ++ expIds program := by
  have main : ∀ n, ∀ program : Prog α, sizeOf program = n → ∀ pre,
      expIds (seqAssoc pre program) = expIds pre ++ expIds program := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hsize pre
      cases program with
      | skip => simp [seqAssoc, expIds]
      | dec name shape value body =>
          rw [seqAssoc.eq_2, expIds_smartSeq]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl (.skip : Prog α)
          simp [expIds, hbody]
      | seq first second =>
          rw [seqAssoc.eq_3]
          have hfirst := ih (sizeOf first) (by rw [← hsize]; decreasing_trivial) first rfl pre
          have hsecond := ih (sizeOf second) (by rw [← hsize]; decreasing_trivial) second rfl (seqAssoc pre first)
          rw [hsecond, hfirst]
          simp [expIds, List.append_assoc]
      | ite condition thenBranch elseBranch =>
          rw [seqAssoc.eq_4, expIds_smartSeq]
          have hthen := ih (sizeOf thenBranch) (by rw [← hsize]; decreasing_trivial) thenBranch rfl (.skip : Prog α)
          have helse := ih (sizeOf elseBranch) (by rw [← hsize]; decreasing_trivial) elseBranch rfl (.skip : Prog α)
          simp [expIds, hthen, helse]
      | «while» condition body =>
          rw [seqAssoc.eq_5, expIds_smartSeq]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl (.skip : Prog α)
          simp [expIds, hbody]
      | call info function arguments =>
          cases info with
          | none => rw [seqAssoc.eq_6, expIds_smartSeq]
          | some returnsHandler =>
              obtain ⟨returns, handlerInfo⟩ := returnsHandler
              cases handlerInfo with
              | none => rw [seqAssoc.eq_7, expIds_smartSeq]
              | some exceptionHandler =>
                  obtain ⟨exception, handlerVar, handler⟩ := exceptionHandler
                  rw [seqAssoc.eq_8, expIds_smartSeq]
                  have hbody := ih (sizeOf handler) (by rw [← hsize]; decreasing_trivial) handler rfl (.skip : Prog α)
                  simp [expIds, hbody]
      | decCall name shape function arguments body =>
          rw [seqAssoc.eq_9, expIds_smartSeq]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl (.skip : Prog α)
          simp [expIds, hbody]
      | annot tag text => simp [seqAssoc, expIds]
      | assign kind name value => simp [seqAssoc, expIds_smartSeq, expIds]
      | primitive name operator arguments => simp [seqAssoc, expIds_smartSeq, expIds]
      | store address value => simp [seqAssoc, expIds_smartSeq, expIds]
      | store32 address value => simp [seqAssoc, expIds_smartSeq, expIds]
      | storeByte address value => simp [seqAssoc, expIds_smartSeq, expIds]
      | «break» => simp [seqAssoc, expIds_smartSeq, expIds]
      | «continue» => simp [seqAssoc, expIds_smartSeq, expIds]
      | extCall function configuration configurationLength array arrayLength =>
          simp [seqAssoc, expIds_smartSeq, expIds]
      | «raise» exception value => simp [seqAssoc, expIds_smartSeq, expIds]
      | «return» value => simp [seqAssoc, expIds_smartSeq, expIds]
      | shMemLoad size kind name address => simp [seqAssoc, expIds_smartSeq, expIds]
      | shMemStore size address value => simp [seqAssoc, expIds_smartSeq, expIds]
      | tick => simp [seqAssoc, expIds_smartSeq, expIds]
  exact main (sizeOf program) program rfl pre

/-- `ret_to_tail` preserves the exception identifiers collected by the source
    program (Cake's `exp_ids_ret_to_tail_eq`).  Same well-founded-recursion
    workaround as `expIds_seqAssoc`. -/
theorem expIds_retToTail (program : Prog α) :
    expIds (retToTail program) = expIds program := by
  have main : ∀ n, ∀ program : Prog α, sizeOf program = n →
      expIds (retToTail program) = expIds program := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hsize
      cases program with
      | skip => simp [retToTail, expIds]
      | dec name shape value body =>
          rw [retToTail.eq_2]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl
          simp [expIds, hbody]
      | seq first second =>
          rw [retToTail.eq_3, expIds_seqCallRet]
          have hfirst := ih (sizeOf first) (by rw [← hsize]; decreasing_trivial) first rfl
          have hsecond := ih (sizeOf second) (by rw [← hsize]; decreasing_trivial) second rfl
          simp [expIds, hfirst, hsecond]
      | ite condition thenBranch elseBranch =>
          rw [retToTail.eq_4]
          have hthen := ih (sizeOf thenBranch) (by rw [← hsize]; decreasing_trivial) thenBranch rfl
          have helse := ih (sizeOf elseBranch) (by rw [← hsize]; decreasing_trivial) elseBranch rfl
          simp [expIds, hthen, helse]
      | «while» condition body =>
          rw [retToTail.eq_5]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl
          simp [expIds, hbody]
      | call info function arguments =>
          cases info with
          | none => rw [retToTail.eq_6]
          | some returnsHandler =>
              obtain ⟨returns, handlerInfo⟩ := returnsHandler
              cases handlerInfo with
              | none => rw [retToTail.eq_7]
              | some exceptionHandler =>
                  obtain ⟨exception, handlerVar, handler⟩ := exceptionHandler
                  rw [retToTail.eq_8]
                  have hbody := ih (sizeOf handler) (by rw [← hsize]; decreasing_trivial) handler rfl
                  simp [expIds, hbody]
      | decCall name shape function arguments body =>
          rw [retToTail.eq_9]
          have hbody := ih (sizeOf body) (by rw [← hsize]; decreasing_trivial) body rfl
          simp [expIds, hbody]
      | annot tag text => simp [retToTail, expIds]
      | assign kind name value => simp [retToTail, expIds]
      | primitive name operator arguments => simp [retToTail, expIds]
      | store address value => simp [retToTail, expIds]
      | store32 address value => simp [retToTail, expIds]
      | storeByte address value => simp [retToTail, expIds]
      | «break» => simp [retToTail, expIds]
      | «continue» => simp [retToTail, expIds]
      | extCall function configuration configurationLength array arrayLength =>
          simp [retToTail, expIds]
      | «raise» exception value => simp [retToTail, expIds]
      | «return» value => simp [retToTail, expIds]
      | shMemLoad size kind name address => simp [retToTail, expIds]
      | shMemStore size address value => simp [retToTail, expIds]
      | tick => simp [retToTail, expIds]
  exact main (sizeOf program) program rfl

/-- The full `pan_simp` program pass preserves the exception identifiers
    collected by the source program (Cake's `exp_ids_compile_eq`). -/
theorem expIds_panSimpProg (program : Prog α) :
    expIds (panSimpProg program) = expIds program := by
  unfold panSimpProg
  rw [expIds_retToTail, expIds_seqAssoc]
  simp [expIds]

end Flapjack
