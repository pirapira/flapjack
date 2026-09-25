import Flapjack.Pancake.PanLang

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
    declarations dropped.  This is an alias for the production `functionEntries`
    (`Flapjack/Pancake/PanLang.lean`); that mirror is deliberately untagged
    because its carriers are generic `Decl α` with String-backed names and
    monomorphic `Shape`/`Prog α`, not HOL's word-indexed `decl` with `mlstring`
    identifiers (bead `flapjack-pxn.18.3.5.8`).  The executable path and the
    production definition coincide. -/
abbrev functions :
    List (Decl α) → List (FunName × List (VarName × Shape) × Prog α × Shape) :=
  functionEntries

/-- Counterpart of Cake's `functions_eq_FILTER`
    (`cakeml/pancake/semantics/panPropsScript.sml:1487`): the function table is
    exactly the projection of the function declarations, with every other
    declaration contributing nothing.  Cake writes the projection as a `MAP`
    over `FILTER is_function` with an `ARB` default branch; `List.filterMap`
    states the same content without needing a default value.

    FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag): beyond the
    identifier carrier (production `Decl α`/`Prog α` are generic in the word
    element type and use `FunName = String`, while HOL `decl` is word-indexed
    with `funname`/`varname`/`eid`/`stcname` = `mlstring`), the statement is
    not HOL's: HOL maps the tuple projection over `FILTER is_function` with an
    unspecified `ARB` fallback on non-function declarations, whereas
    `List.filterMap` drops those declarations via `none` instead of producing
    an `ARB` tuple.  Rendering `ARB` faithfully (and an exact `functions`
    over `List (DeclHOL width)`) is tracked by `flapjack-4ac.4.109`, itself
    gated on the exact MlString/width-indexed carriers of
    `flapjack-pxn.18.3.5.8`. -/
theorem functions_eq_filterMap (declarations : List (Decl α)) :
    functions declarations =
      declarations.filterMap (fun declaration =>
        match declaration with
        | .function function =>
            some (function.name, function.params, function.body,
              function.returnShape)
        | _ => none) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;> simp [functions, functionEntries, ih]

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
  | nil => simp [panSimpDecls, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panSimpDecls, functions, functionEntries, ih]

/-! Cake's `MEM_functions` (`pan_globalsProofScript.sml:2380`): every entry of
    the `functions` projection comes from a function declaration of the source
    list, with the entry being that declaration's name, parameters, body, and
    return shape. -/
theorem mem_functions {declarations : List (Decl α)}
    {entry : FunName × List (VarName × Shape) × Prog α × Shape}
    (hmem : entry ∈ functions declarations) :
    ∃ declaration : FunDecl α,
      (.function declaration : Decl α) ∈ declarations ∧
        entry = (declaration.name, declaration.params, declaration.body,
          declaration.returnShape) := by
  induction declarations with
  | nil => simp [functions, functionEntries] at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [functions, functionEntries, List.mem_cons] at hmem
          rcases hmem with hentry | htail
          · subst hentry
            exact ⟨function, by simp, rfl⟩
          · obtain ⟨found, hfound, hentry⟩ := ih htail
            exact ⟨found, by simp [hfound], hentry⟩
      | decl shape name value =>
          simp only [functions, functionEntries] at hmem
          obtain ⟨found, hfound, hentry⟩ := ih hmem
          exact ⟨found, by simp [hfound], hentry⟩
      | exnDecl exception shape =>
          simp only [functions, functionEntries] at hmem
          obtain ⟨found, hfound, hentry⟩ := ih hmem
          exact ⟨found, by simp [hfound], hentry⟩
      | name struct fields =>
          simp only [functions, functionEntries] at hmem
          obtain ⟨found, hfound, hentry⟩ := ih hmem
          exact ⟨found, by simp [hfound], hentry⟩

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

/-! Counterpart of Cake's `compile_prog_distinct_params`
    (`pan_simpProofScript.sml:1064-1069`): rewriting function bodies does not
    alter the parameter names of any function declaration.  Flapjack keeps
    parameter shapes alongside names, so the invariant is stated for the
    projected name list. -/
theorem functions_panSimpDecls_params_nodup (declarations : List (Decl α))
    (hparams : ∀ entry ∈ functions declarations,
      (entry.2.1.map Prod.fst).Nodup) :
    ∀ entry ∈ functions (panSimpDecls declarations),
      (entry.2.1.map Prod.fst).Nodup := by
  rw [functions_panSimpDecls]
  intro entry hentry
  simp only [List.mem_map] at hentry
  obtain ⟨source, hsource, rfl⟩ := hentry
  exact hparams source hsource

/-- Counterpart of the original `ALOOKUP` on the function table
    (`panLangScript.sml:319-326`): first-occurrence lookup of a function name in
    the `(name, params, body, returnShape)` projection `functions` produces. -/
def lookupFunctionEntry (name : FunName) :
    List (FunName × List (VarName × Shape) × Prog α × Shape) →
      Option (List (VarName × Shape) × Prog α × Shape)
  | [] => none
  | entry :: functions =>
      if name == entry.1 then some (entry.2.1, entry.2.2.1, entry.2.2.2)
      else lookupFunctionEntry name functions

/-! Counterpart of the function-table lookup fact used by Cake's
    `state_rel_imp_semantics` (`pan_simpProofScript.sml:1073-1300`): a
    successful lookup in the source table succeeds at the same name,
    parameters, and return shape after `pan_simp`, with only the body
    transformed. -/
theorem lookupFunctionEntry_panSimpDecls
    (declarations : List (Decl α)) (name : FunName)
    {parameters : List (VarName × Shape)} {body : Prog α} {returnShape : Shape}
    (hlookup : lookupFunctionEntry name (functions declarations) =
      some (parameters, body, returnShape)) :
    lookupFunctionEntry name (functions (panSimpDecls declarations)) =
      some (parameters, panSimpProg body, returnShape) := by
  induction declarations with
  | nil =>
      simp [functions, functionEntries, lookupFunctionEntry] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name == declaration.name
          · simp [functions, functionEntries, panSimpDecls, lookupFunctionEntry, hname] at hlookup ⊢
            rcases hlookup with ⟨rfl, rfl, rfl⟩
            simp
          · have htail : lookupFunctionEntry name (functions declarations) =
                some (parameters, body, returnShape) := by
              simpa [functions, functionEntries, lookupFunctionEntry, hname] using hlookup
            have htail' := ih htail
            simpa [functions, functionEntries, panSimpDecls, lookupFunctionEntry, hname]
              using htail'
      | decl shape declarationName expression =>
          have htail : lookupFunctionEntry name (functions declarations) =
              some (parameters, body, returnShape) := by
            simpa only [functions, functionEntries] using hlookup
          simpa only [panSimpDecls, functions, functionEntries] using ih htail
      | exnDecl exception shape =>
          have htail : lookupFunctionEntry name (functions declarations) =
              some (parameters, body, returnShape) := by
            simpa only [functions, functionEntries] using hlookup
          simpa only [panSimpDecls, functions, functionEntries] using ih htail
      | name struct fields =>
          have htail : lookupFunctionEntry name (functions declarations) =
              some (parameters, body, returnShape) := by
            simpa only [functions, functionEntries] using hlookup
          simpa only [panSimpDecls, functions, functionEntries] using ih htail

/-- `lookupFunctionEntry` returns the entry found at a given index whenever the
    function names are distinct. -/
theorem lookupFunctionEntry_of_getElem?
    (functions : List (FunName × List (VarName × Shape) × Prog α × Shape))
    (hnodup : (functions.map (fun entry => entry.1)).Nodup)
    {n : Nat} {entry : FunName × List (VarName × Shape) × Prog α × Shape}
    (hget : functions[n]? = some entry) :
    lookupFunctionEntry entry.1 functions =
      some (entry.2.1, entry.2.2.1, entry.2.2.2) := by
  induction functions generalizing n with
  | nil => simp at hget
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hhead, htail⟩ := hnodup
      cases n with
      | zero =>
          rw [List.getElem?_cons_zero] at hget
          simp only [Option.some.injEq] at hget
          subst hget
          simp [lookupFunctionEntry]
      | succ n =>
          rw [List.getElem?_cons_succ] at hget
          have hentry_mem : entry.1 ∈ tail.map (fun entry => entry.1) := by
            obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
            rw [← heq]
            exact List.mem_map.mpr ⟨tail[n], List.getElem_mem hlt, rfl⟩
          have hne : entry.1 ≠ head.1 := fun h => hhead (h ▸ hentry_mem)
          simp only [lookupFunctionEntry]
          rw [if_neg (by simpa [beq_iff_eq] using hne)]
          exact ih htail hget

/-- Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_simpProofScript.sml:1047-1061`): the compiled function table only
    rewrites bodies, so an entry at a given index still comes from the source
    table. -/
theorem el_functions_panSimpDecls_eq {declarations : List (Decl α)} {n : Nat}
    {start : FunName} {pprog p : Prog α} {rshape : Shape}
    (hentry : (functions (panSimpDecls declarations))[n]? =
      some (start, [], pprog, rshape))
    (hnodup : ((functions declarations).map (fun entry => entry.1)).Nodup)
    (_hlen : n < (functions declarations).length)
    (hlookup : lookupFunctionEntry start (functions declarations) =
      some ([], p, rshape)) :
    (functions declarations)[n]? = some (start, [], p, rshape) := by
  rw [functions_panSimpDecls, List.getElem?_map] at hentry
  have hsome : (functions declarations)[n]? ≠ none := by
    intro hnone
    rw [hnone] at hentry
    exact absurd hentry (by simp)
  obtain ⟨entry, hentry_eq⟩ := Option.ne_none_iff_exists'.mp hsome
  have hproj :
      (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2) =
        (start, [], pprog, rshape) := by
    rw [hentry_eq] at hentry
    simpa using hentry
  have h1 : entry.1 = start := by
    simpa using congrArg Prod.fst hproj
  have hlookupEntry :=
    lookupFunctionEntry_of_getElem? (functions declarations) hnodup hentry_eq
  rw [h1] at hlookupEntry
  rw [hlookup] at hlookupEntry
  have hp : (entry.2.1, entry.2.2.1, entry.2.2.2) = ([], p, rshape) :=
    (Option.some.inj hlookupEntry).symm
  have g1 : entry.2.1 = [] := by simpa using congrArg Prod.fst hp
  have g2 : entry.2.2.1 = p := by
    simpa using congrArg Prod.fst (congrArg Prod.snd hp)
  have g3 : entry.2.2.2 = rshape := by
    simpa using congrArg Prod.snd (congrArg Prod.snd hp)
  rw [hentry_eq]
  congr 1
  refine Prod.ext (by simpa using h1) ?_
  refine Prod.ext (by simpa using g1) ?_
  exact Prod.ext (by simpa using g2) (by simpa using g3)

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

/-- The exception identifiers reachable from the bodies of the function
    declarations in a declaration table: the projection that Cake's `get_eids`
    scans. -/
def declarationExceptionIds : List (Decl α) → List ExceptionId
  | [] => []
  | .function declaration :: declarations =>
      expIds declaration.body ++ declarationExceptionIds declarations
  | _ :: declarations => declarationExceptionIds declarations

/-- The declaration-table pass of `pan_simp` preserves the exception
    identifiers reachable from every function body.  This is the source-side
    companion of Cake's `get_eids_from_decls` invariance: the finite domain of
    the exception table cannot change when the bodies are simplified. -/
theorem declarationExceptionIds_panSimpDecls (declarations : List (Decl α)) :
    declarationExceptionIds (panSimpDecls declarations) =
      declarationExceptionIds declarations := by
  induction declarations with
  | nil => simp [panSimpDecls, declarationExceptionIds]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panSimpDecls, declarationExceptionIds, expIds_panSimpProg, ih]

/-- The function-only projection of the declaration table is exactly the flat
    map of `expIds` over the function bodies, which is the list that Cake's
    `get_eids` numbers before removing repeats. -/
theorem declarationExceptionIds_map_function (functions : List (FunDecl α)) :
    declarationExceptionIds (functions.map (fun function => Decl.function function)) =
      functions.flatMap (fun function => expIds function.body) := by
  induction functions with
  | nil => simp [declarationExceptionIds]
  | cons function functions ih => simp [declarationExceptionIds, ih]

/-! ## A linear syntactic size bound for `seqAssoc`

`seqAssoc` only reassociates sequences and never duplicates syntax, so a
simple node-count measure grows by a constant factor.  This is the syntactic
ingredient needed to turn the clocked evaluator's per-constructor success
equations into a uniform `C(sizeOf program)` fuel adequacy statement. -/

def progSize : Prog α → Nat
  | .skip => 1
  | .dec _ _ _ body => 1 + progSize body
  | .seq first second => 1 + progSize first + progSize second
  | .ite _ thenBranch elseBranch => 1 + progSize thenBranch + progSize elseBranch
  | .while _ body => 1 + progSize body
  | .call info _ _ =>
      match info with
      | none => 1
      | some (_, none) => 1
      | some (_, some (_, _, handler)) => 1 + progSize handler
  | .decCall _ _ _ _ body => 1 + progSize body
  | .annot _ _ => 1
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! `ret_to_tail` only removes the assign/return wrapper used for a tail call;
    it does not add program nodes.  This small syntactic fact is used by the
    evaluator-level `pan_simp` fuel bound. -/

theorem progSize_seqCallRet_le (program : Prog α) :
    progSize (seqCallRet program) ≤ progSize program := by
  cases program with
  | seq first second =>
      cases first with
      | call info function arguments =>
          cases second with
          | «return» value =>
              cases value with
              | var kind returnedName =>
                  cases kind with
                  | «local» =>
                      cases info with
                      | none => simp [seqCallRet, progSize]
                      | some info =>
                          cases info with
                          | mk returns handler =>
                              cases returns with
                              | none => simp [seqCallRet, progSize]
                              | some returnInfo =>
                                  cases returnInfo with
                                  | mk returnKind returnName =>
                                      cases returnKind with
                                      | «local» =>
                                          cases handler with
                                          | none =>
                                              simp [seqCallRet, progSize] <;>
                                                split <;> simp [progSize]
                                          | some handler => simp [seqCallRet, progSize]
                                      | global => simp [seqCallRet, progSize]
                  | global => simp [seqCallRet, progSize]
              | _ => simp [seqCallRet, progSize]
          | _ => simp [seqCallRet, progSize]
      | _ => simp [seqCallRet, progSize]
  | _ => simp [seqCallRet, progSize]

theorem progSize_retToTail_le (program : Prog α) :
    progSize (retToTail program) ≤ progSize program := by
  let rec go : (program : Prog α) → progSize (retToTail program) ≤ progSize program
    | .skip => by simp [retToTail, progSize]
    | .dec name shape value body => by
        have h := go body
        simp [retToTail, progSize]
        omega
    | .assign kind name value => by simp [retToTail, progSize]
    | .primitive name operator args => by simp [retToTail, progSize]
    | .store address value => by simp [retToTail, progSize]
    | .store32 address value => by simp [retToTail, progSize]
    | .storeByte address value => by simp [retToTail, progSize]
    | .seq first second => by
        have hfirst := go first
        have hsecond := go second
        calc
          progSize (retToTail (.seq first second)) =
              progSize (seqCallRet (.seq (retToTail first) (retToTail second))) := by
                simp only [retToTail]
          _ ≤ progSize (.seq (retToTail first) (retToTail second)) :=
            progSize_seqCallRet_le _
          _ = 1 + progSize (retToTail first) + progSize (retToTail second) := by
            simp [progSize]
          _ ≤ 1 + progSize first + progSize second := by omega
          _ = progSize (.seq first second) := by simp [progSize]
    | .ite condition thenBranch elseBranch => by
        simp only [retToTail, progSize]
        have hthen := go thenBranch
        have helse := go elseBranch
        omega
    | .while condition body => by
        have h := go body
        simp [retToTail, progSize]
        omega
    | .break => by simp [retToTail, progSize]
    | .continue => by simp [retToTail, progSize]
    | .call info name args => by
        cases info with
        | none => simp [retToTail, progSize]
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none => simp [retToTail, progSize]
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            have h := go handlerProgram
                            simp [retToTail, progSize]
                            omega
    | .decCall name shape function args body => by
        have h := go body
        simp [retToTail, progSize]
        omega
    | .extCall function configuration configurationLength array arrayLength =>
        by simp [retToTail, progSize]
    | .raise exception value => by simp [retToTail, progSize]
    | .return value => by simp [retToTail, progSize]
    | .shMemLoad size kind name address => by simp [retToTail, progSize]
    | .shMemStore size address value => by simp [retToTail, progSize]
    | .tick => by simp [retToTail, progSize]
    | .annot tag text => by simp [retToTail, progSize]
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program

theorem progSize_pos : ∀ program : Prog α, 1 ≤ progSize program
  | .dec _ _ _ _ => by simp only [progSize]; omega
  | .seq _ _ => by simp only [progSize]; omega
  | .ite _ _ _ => by simp only [progSize]; omega
  | .while _ _ => by simp only [progSize]; omega
  | .call info _ _ => by
      cases info with
      | none => simp only [progSize]; omega
      | some info =>
          cases info with
          | mk returns handlerInfo =>
              cases handlerInfo with
              | none => simp only [progSize]; omega
              | some handler =>
                  cases handler with
                  | mk exception handlerInfo =>
                      cases handlerInfo with
                      | mk handlerVar handlerProgram =>
                          simp only [progSize]; omega
  | .decCall _ _ _ _ _ => by simp only [progSize]; omega
  | .skip => by simp only [progSize]; omega
  | .annot _ _ => by simp only [progSize]; omega
  | .assign _ _ _ => by simp only [progSize]; omega
  | .primitive _ _ _ => by simp only [progSize]; omega
  | .store _ _ => by simp only [progSize]; omega
  | .store32 _ _ => by simp only [progSize]; omega
  | .storeByte _ _ => by simp only [progSize]; omega
  | .break => by simp only [progSize]; omega
  | .continue => by simp only [progSize]; omega
  | .extCall _ _ _ _ _ => by simp only [progSize]; omega
  | .raise _ _ => by simp only [progSize]; omega
  | .return _ => by simp only [progSize]; omega
  | .shMemLoad _ _ _ _ => by simp only [progSize]; omega
  | .shMemStore _ _ _ => by simp only [progSize]; omega
  | .tick => by simp only [progSize]; omega

/-- A call-aware structural budget: `progSize` for the ordinary nodes, but each
    `Call`/`DecCall` node reserves a uniform `callBudget` for its callee (and
    `max` with the handler or continuation body where those run at the same
    fuel).  This is the budget the program-level adequacy statement needs, since
    `progSize` charges only one unit for a `Call` node and does not cover the
    callee or handler bodies. -/
def progCallFuel (callBudget : Nat) : Prog α → Nat
  | .skip => 1
  | .dec _ _ _ body => 1 + progCallFuel callBudget body
  | .seq first second =>
      1 + progCallFuel callBudget first + progCallFuel callBudget second
  | .ite _ thenBranch elseBranch =>
      1 + progCallFuel callBudget thenBranch + progCallFuel callBudget elseBranch
  | .while _ body => 1 + progCallFuel callBudget body
  | .call none _ _ => 1 + callBudget
  | .call (some (_, none)) _ _ => 1 + callBudget
  | .call (some (_, some (_, _, handler))) _ _ =>
      1 + max callBudget (progCallFuel callBudget handler)
  | .decCall _ _ _ _ body => 1 + max callBudget (progCallFuel callBudget body)
  | .annot _ _ => 1
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- The call-aware budget dominates the plain structural size. -/
theorem progSize_le_progCallFuel (callBudget : Nat) (program : Prog α) :
    progSize program ≤ progCallFuel callBudget program := by
  let rec go : (program : Prog α) →
      progSize program ≤ progCallFuel callBudget program
    | .skip => by simp only [progSize, progCallFuel]; omega
    | .dec _ _ _ body => by
        simp only [progSize, progCallFuel]
        have hb := go body
        omega
    | .seq first second => by
        simp only [progSize, progCallFuel]
        have h1 := go first
        have h2 := go second
        omega
    | .ite _ thenBranch elseBranch => by
        simp only [progSize, progCallFuel]
        have ht := go thenBranch
        have he := go elseBranch
        omega
    | .while _ body => by
        simp only [progSize, progCallFuel]
        have hb := go body
        omega
    | .call info _ _ => by
        cases info with
        | none => simp only [progSize, progCallFuel]; omega
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none => simp only [progSize, progCallFuel]; omega
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [progSize, progCallFuel]
                            have hh := go handlerProgram
                            omega
    | .decCall _ _ _ _ body => by
        simp only [progSize, progCallFuel]
        have hb := go body
        omega
    | .annot _ _ => by simp only [progSize, progCallFuel]; omega
    | .assign _ _ _ => by simp only [progSize, progCallFuel]; omega
    | .primitive _ _ _ => by simp only [progSize, progCallFuel]; omega
    | .store _ _ => by simp only [progSize, progCallFuel]; omega
    | .store32 _ _ => by simp only [progSize, progCallFuel]; omega
    | .storeByte _ _ => by simp only [progSize, progCallFuel]; omega
    | .break => by simp only [progSize, progCallFuel]; omega
    | .continue => by simp only [progSize, progCallFuel]; omega
    | .extCall _ _ _ _ _ => by simp only [progSize, progCallFuel]; omega
    | .raise _ _ => by simp only [progSize, progCallFuel]; omega
    | .return _ => by simp only [progSize, progCallFuel]; omega
    | .shMemLoad _ _ _ _ => by simp only [progSize, progCallFuel]; omega
    | .shMemStore _ _ _ => by simp only [progSize, progCallFuel]; omega
    | .tick => by simp only [progSize, progCallFuel]; omega
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program

theorem progSize_smartSeq_le (pre program : Prog α) :
    progSize (smartSeq pre program) ≤ progSize pre + progSize program + 1 := by
  unfold smartSeq
  split
  · simp only [progSize]
    omega
  · simp only [progSize]
    omega

theorem progSize_seqAssoc_le (pre program : Prog α) :
    progSize (seqAssoc pre program) ≤ progSize pre + 4 * progSize program := by
  let rec go (pre : Prog α) : (program : Prog α) →
      progSize (seqAssoc pre program) ≤ progSize pre + 4 * progSize program
    | .skip => by simp [seqAssoc, progSize]
    | .dec name shape value body => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.dec name shape value (seqAssoc .skip body))
        have hb := go .skip body
        simp only [progSize] at h hb ⊢
        omega
    | .seq first second => by
        simp only [seqAssoc, progSize]
        have h1 := go (seqAssoc pre first) second
        have h2 := go pre first
        omega
    | .ite condition thenBranch elseBranch => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre
          (.ite condition (seqAssoc .skip thenBranch) (seqAssoc .skip elseBranch))
        have ht := go .skip thenBranch
        have he := go .skip elseBranch
        simp only [progSize] at h ht he ⊢
        omega
    | .while condition body => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.while condition (seqAssoc .skip body))
        have hb := go .skip body
        simp only [progSize] at h hb ⊢
        omega
    | .call info function arguments => by
        cases info with
        | none =>
            simp only [seqAssoc]
            have h := progSize_smartSeq_le pre (.call none function arguments)
            simp only [progSize] at h ⊢
            omega
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none =>
                    simp only [seqAssoc]
                    have h := progSize_smartSeq_le pre
                      (.call (some (returns, none)) function arguments)
                    simp only [progSize] at h ⊢
                    omega
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [seqAssoc]
                            have h := progSize_smartSeq_le pre
                              (.call (some (returns, some (exception, handlerVar,
                                seqAssoc .skip handlerProgram))) function arguments)
                            have hb := go .skip handlerProgram
                            simp only [progSize] at h hb ⊢
                            omega
    | .decCall name shape function arguments body => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre
          (.decCall name shape function arguments (seqAssoc .skip body))
        have hb := go .skip body
        simp only [progSize] at h hb ⊢
        omega
    | .annot tag text => by simp [seqAssoc, progSize]
    | .assign kind name value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.assign kind name value)
        simp only [progSize] at h ⊢
        omega
    | .primitive name operator args => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.primitive name operator args)
        simp only [progSize] at h ⊢
        omega
    | .store address value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.store address value)
        simp only [progSize] at h ⊢
        omega
    | .store32 address value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.store32 address value)
        simp only [progSize] at h ⊢
        omega
    | .storeByte address value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.storeByte address value)
        simp only [progSize] at h ⊢
        omega
    | .break => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.break : Prog α)
        simp only [progSize] at h ⊢
        omega
    | .continue => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.continue : Prog α)
        simp only [progSize] at h ⊢
        omega
    | .extCall function configuration configurationLength array arrayLength => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre
          (.extCall function configuration configurationLength array arrayLength)
        simp only [progSize] at h ⊢
        omega
    | .raise exception value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.raise exception value)
        simp only [progSize] at h ⊢
        omega
    | .return value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.return value)
        simp only [progSize] at h ⊢
        omega
    | .shMemLoad size kind name address => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.shMemLoad size kind name address)
        simp only [progSize] at h ⊢
        omega
    | .shMemStore size address value => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.shMemStore size address value)
        simp only [progSize] at h ⊢
        omega
    | .tick => by
        simp only [seqAssoc]
        have h := progSize_smartSeq_le pre (.tick : Prog α)
        simp only [progSize] at h ⊢
        omega
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre program

theorem progSize_panSimpProg_le (program : Prog α) :
    progSize (panSimpProg program) ≤ 1 + 4 * progSize program := by
  simp only [panSimpProg]
  exact Nat.le_trans (progSize_retToTail_le (seqAssoc .skip program))
    (by simpa [progSize] using progSize_seqAssoc_le (.skip : Prog α) program)

end Flapjack
