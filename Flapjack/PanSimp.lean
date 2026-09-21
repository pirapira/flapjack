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

def panSimpDecl : Decl α → Decl α
  | .function declaration =>
      .function { declaration with body := panSimpProg declaration.body }
  | declaration => declaration

/-! Cake's `functions` projection (`panLangScript.sml:319-326`): the function
    table as `(name, params, body, returnShape)` entries, with non-function
    declarations dropped. -/
def functions :
    List (Decl α) → List (FunName × List (VarName × Shape) × Prog α × Shape)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, declaration.params, declaration.body,
        declaration.returnShape) :: functions declarations
  | _ :: declarations => functions declarations

/-! Source-shaped counterpart of Cake's `compile_prog_pmatch`: `compile_prog`
    maps `compile` over function declarations and leaves other declarations
    unchanged. -/
theorem panSimpDecls_eq_map (declarations : List (Decl α)) :
    panSimpDecls declarations = declarations.map panSimpDecl := by
  induction declarations with
  | nil => simp [panSimpDecls]
  | cons declaration declarations ih =>
      cases declaration <;> simp [panSimpDecls, panSimpDecl, ih]

/-! Counterpart of Cake's `functions_compile_prog`
    (`pan_simpProofScript.sml:1017-1022`): `pan_simp` rewrites each function
    body through `panSimpProg` and leaves the name, parameters, and return
    shape unchanged. -/
theorem functions_panSimpDecls (declarations : List (Decl α)) :
    functions (panSimpDecls declarations) =
      (functions declarations).map (fun entry =>
        (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2)) := by
  induction declarations with
  | nil => simp [panSimpDecls, functions]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panSimpDecls, functions, ih]

/-! Counterpart of Cake's `first_compile_prog_all_distinct`
    (`pan_simpProofScript.sml:1025-1041`): `pan_simp` preserves distinctness of
    the function-name table.  This is the invariant `state_rel_imp_semantics`
    needs for the compiled program. -/
theorem functions_panSimpDecls_names_nodup (declarations : List (Decl α))
    (hnames : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions (panSimpDecls declarations)).map (fun entry => entry.1)).Nodup := by
  rw [functions_panSimpDecls, List.map_map]
  have hfun :
      ((fun entry : FunName × List (VarName × Shape) × Prog α × Shape => entry.1) ∘
        (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
          (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2))) =
      (fun entry : FunName × List (VarName × Shape) × Prog α × Shape => entry.1) := by
    funext entry
    rfl
  rw [hfun]
  exact hnames

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

/-! Manual well-founded induction for Cake's `exp_ids_ret_to_tail_eq`.  The
    handler stored inside `Call` is nested in the syntax, so this uses the
    same explicit handler case as `expIds_seqAssoc`. -/

theorem expIds_retToTail (program : Prog α) :
    expIds (retToTail program) = expIds program := by
  let rec go : (program : Prog α) →
      expIds (retToTail program) = expIds program
    | .skip => by
        simp [retToTail, expIds]
    | .dec name shape value body => by
        simp only [retToTail, expIds]
        rw [go body]
    | .seq first second => by
        simp only [retToTail]
        rw [expIds_seqCallRet]
        simp only [expIds]
        rw [go first, go second]
    | .ite condition thenBranch elseBranch => by
        simp only [retToTail, expIds]
        rw [go thenBranch, go elseBranch]
    | .while condition body => by
        simp only [retToTail, expIds]
        rw [go body]
    | .call info function arguments => by
        cases info with
        | none =>
            simp [retToTail, expIds]
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none =>
                    simp [retToTail, expIds]
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [retToTail]
                            simp only [expIds]
                            rw [go handlerProgram]
    | .decCall name shape function arguments body => by
        simp only [retToTail, expIds]
        rw [go body]
    | .annot tag text => by
        simp [retToTail, expIds]
    | .assign kind name value => by
        simp [retToTail, expIds]
    | .primitive name operator args => by
        simp [retToTail, expIds]
    | .store address value => by
        simp [retToTail, expIds]
    | .store32 address value => by
        simp [retToTail, expIds]
    | .storeByte address value => by
        simp [retToTail, expIds]
    | .break => by
        simp [retToTail, expIds]
    | .continue => by
        simp [retToTail, expIds]
    | .extCall function configuration configurationLength array arrayLength => by
        simp [retToTail, expIds]
    | .raise exception value => by
        simp [retToTail, expIds]
    | .return value => by
        simp [retToTail, expIds]
    | .shMemLoad size kind name address => by
        simp [retToTail, expIds]
    | .shMemStore size address value => by
        simp [retToTail, expIds]
    | .tick => by
        simp [retToTail, expIds]
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program

/-- The full `pan_simp` program transformation preserves the exception
    identifiers reachable from a program, mirroring Cake's
    `exp_ids_compile_eq`. -/
theorem expIds_panSimpProg (program : Prog α) :
    expIds (panSimpProg program) = expIds program := by
  simp only [panSimpProg]
  rw [expIds_retToTail, expIds_seqAssoc]
  simp [expIds]

end Flapjack
