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

/-! Manual well-founded induction for Cake's `exp_ids_seq_assoc_eq`.  The
    handler stored inside `Call` is nested in the syntax, so the ordinary
    generated `Prog` recursor does not expose it as an induction hypothesis. -/

theorem expIds_seqAssoc (pre program : Prog α) :
    expIds (seqAssoc pre program) = expIds pre ++ expIds program := by
  let rec go (pre : Prog α) : (program : Prog α) →
      expIds (seqAssoc pre program) = expIds pre ++ expIds program
    | .skip => by
        simp [seqAssoc, expIds]
    | .dec name shape value body => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
        simp only [expIds]
        rw [go .skip body]
        simp [expIds]
    | .seq first second => by
        simp only [seqAssoc]
        rw [go (seqAssoc pre first) second, go pre first]
        simp [expIds, List.append_assoc]
    | .ite condition thenBranch elseBranch => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
        simp only [expIds]
        rw [go .skip thenBranch, go .skip elseBranch]
        simp [expIds]
    | .while condition body => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
        simp only [expIds]
        rw [go .skip body]
        simp [expIds]
    | .call info function arguments => by
        cases info with
        | none =>
            simp [seqAssoc, expIds, expIds_smartSeq]
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none =>
                    simp [seqAssoc, expIds, expIds_smartSeq]
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [seqAssoc]
                            rw [expIds_smartSeq]
                            simp only [expIds]
                            rw [go .skip handlerProgram]
                            simp [expIds]
    | .decCall name shape function arguments body => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
        simp only [expIds]
        rw [go .skip body]
        simp [expIds]
    | .annot tag text => by
        simp [seqAssoc, expIds]
    | .assign kind name value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .primitive name operator args => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .store address value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .store32 address value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .storeByte address value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .break => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .continue => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .extCall function configuration configurationLength array arrayLength => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .raise exception value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .return value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .shMemLoad size kind name address => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .shMemStore size address value => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    | .tick => by
        simp only [seqAssoc]
        rw [expIds_smartSeq]
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre program

end Flapjack
