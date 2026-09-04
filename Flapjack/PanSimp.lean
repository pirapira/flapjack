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

end Flapjack
