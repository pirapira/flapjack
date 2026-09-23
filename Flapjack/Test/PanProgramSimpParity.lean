import Flapjack.Pancake.Proofs.PanSimp

namespace Flapjack.Test.PanProgramSimpParity

/-! Direct parity for Cake's `decs_stcnames_compile_prog`
    (`pan_simpProofScript.sml:1334-1341`): `pan_simp` must not change the
    struct-name context collected by `decs_stcnames` /
    `collectPanValueStructs`. -/

def fixture : List (Decl Nat) :=
  [.name "S" [("f1", .one), ("f2", .one)],
   .decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

theorem collectPanValueStructs_panSimpDecls_fixture :
    collectPanValueStructs (panSimpDecls fixture) [] =
      collectPanValueStructs fixture [] :=
  collectPanValueStructs_panSimpDecls fixture []

def namesGuard : Bool :=
  match collectPanValueStructs fixture [] with
  | some context => context.map Prod.fst == ["S"]
  | none => false

def parityGuard : Bool :=
  match collectPanValueStructs (panSimpDecls fixture) [],
      collectPanValueStructs fixture [] with
  | some simplified, some original => simplified.map Prod.fst == original.map Prod.fst
  | none, none => true
  | _, _ => false

#eval namesGuard
#guard namesGuard
#eval parityGuard
#guard parityGuard

/-! Focused regressions for the `OPT_MMAP` helper counterparts used by
    `compile_correct` (`pan_simpProofScript.sml:394`, `:500`, `:509`). -/

/-- The `some` branch of `opt_mmap_eq_some_helper`. -/
theorem list_mapM_eq_some_of_eq_some_fixture :
    ([3, 5] : List Nat).mapM (fun n => if n == 4 then none else some (n + 1)) =
      some [4, 6] :=
  list_mapM_eq_some_of_eq_some (fun n : Nat => if n == 4 then none else some (n + 1))
    (fun n : Nat => if n == 4 then none else some (n + 1)) [3, 5] [4, 6] (by decide)
    (fun _ _ _ h => h)

/-- `OPT_MMAP_NONE`: the failing element is `4`. -/
theorem list_mapM_eq_none_exists_fixture :
    ∃ x ∈ ([3, 4, 5] : List Nat),
      (fun n => if n == 4 then none else some (n + 1)) x = none :=
  list_mapM_eq_none_exists (fun n : Nat => if n == 4 then none else some (n + 1)) [3, 4, 5]
    (by decide)

/-- `OPT_MMAP_NONE'`: member `4` makes the whole map fail. -/
theorem list_mapM_eq_none_of_mem_fixture :
    ([3, 4, 5] : List Nat).mapM (fun n => if n == 4 then none else some (n + 1)) =
      none :=
  list_mapM_eq_none_of_mem (f := fun n : Nat => if n == 4 then none else some (n + 1))
    (x := 4) (xs := [3, 4, 5]) (by decide) (by decide)

/-- `opt_mmap_eq_some_el` (`pan_structsProofScript.sml:19`), reverse direction. -/
theorem list_mapM_eq_some_iff_fixture :
    ([3, 5] : List Nat).mapM (fun n => if n == 4 then none else some (n + 1)) =
      some [4, 6] := by
  rw [list_mapM_eq_some_iff]
  refine ⟨by decide, ?_⟩
  intro n hn
  have hn' : n < 2 := by simpa using hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl <;> decide

/-- `opt_mmap_eq_some_el`, forward direction. -/
theorem list_mapM_eq_some_iff_length_fixture :
    ([3, 5] : List Nat).length = ([4, 6] : List Nat).length :=
  ((list_mapM_eq_some_iff (fun n : Nat => if n == 4 then none else some (n + 1)) [3, 5]
    [4, 6]).mp (by decide)).1

/-- `opt_mmap_eq_every` (`pan_structsProofScript.sml:255`). -/
theorem list_mapM_all_of_mem_fixture :
    ([4, 6] : List Nat).all (fun n => decide (n > 3)) = true :=
  list_mapM_all_of_mem (fun n : Nat => if n == 4 then none else some (n + 1))
    (fun n => decide (n > 3)) [3, 5] [4, 6] (by decide)
    (by
      intro x y hx hxy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp_all <;> omega)

/-! Regression for Cake's `state_rel_imp_evaluate_decls`
    (`pan_simpProofScript.sml:1303-1331`): the declaration-level evaluator
    preserves the state relation whose only non-trivial component simplifies
    every function body with `pan_simp`. -/

def relationState : PanValueProgramState Nat :=
  { structs := [], globals := fun _ => none,
    functions := [("f", [], (.seq (.skip : Prog Nat) (.skip : Prog Nat)))],
    returnShapes := [], parameterShapes := [], exceptions := [],
    memory := fun _ => none, baseAddress := 0, topAddress := 0, bytesInWord := 8 }

def relationDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := (.seq (.skip : Prog Nat) (.skip : Prog Nat)), returnShape := .one }]

theorem relationState_self :
    panValueProgramStateRel relationState
      { relationState with
        functions := panValueFunctionsSimp relationState.functions } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem relationDecls_preserved (s' : PanValueProgramState Nat)
    (hs : evalPanValueDeclarations relationState relationDecls = some s') :
    ∃ t', evalPanValueDeclarations
        { relationState with functions := panValueFunctionsSimp relationState.functions }
        (panSimpDecls relationDecls) = some t' ∧ panValueProgramStateRel s' t' :=
  panValueProgramStateRel_evalPanValueDeclarations relationState _ relationState_self
    relationDecls none s' hs

theorem lookupPanFunction_panValueFunctionsSimp_fixture :
    lookupPanFunction "f" (panValueFunctionsSimp relationState.functions) =
      some ([], panSimpProg (.seq (.skip : Prog Nat) (.skip : Prog Nat))) := by
  apply lookupPanFunction_panValueFunctionsSimp relationState.functions "f"
  simp [relationState, lookupPanFunction]

theorem panValueProgramStateRel_lookupPanFunction_fixture :
    lookupPanFunction "f"
        { relationState with functions := panValueFunctionsSimp relationState.functions }.functions =
      some ([], panSimpProg (.seq (.skip : Prog Nat) (.skip : Prog Nat))) := by
  apply panValueProgramStateRel_lookupPanFunction relationState
    { relationState with functions := panValueFunctionsSimp relationState.functions }
    relationState_self "f"
  simp [relationState, lookupPanFunction]

/-! The declaration adequacy package keeps the post-state relation, the
    `pan_simp` callee body, and the exception-table equality together. -/
theorem panValueProgramStateRel_evalDeclarations_adequacy_fixture
    (s' : PanValueProgramState Nat)
    (hs : evalPanValueDeclarations relationState relationDecls = some s')
    (body : Prog Nat)
    (hlookup : lookupPanFunction "f" s'.functions = some ([], body)) :
    ∃ t', evalPanValueDeclarations
        { relationState with functions := panValueFunctionsSimp relationState.functions }
        (panSimpDecls relationDecls) = some t' ∧
      panValueProgramStateRel s' t' ∧
      lookupPanFunction "f" t'.functions = some ([], panSimpProg body) ∧
      s'.exceptions = t'.exceptions := by
  exact panValueProgramStateRel_evalDeclarations_adequacy relationState _
    relationState_self relationDecls none s' hs "f" hlookup

/-! The returned-call declaration bridge projects only the return-shape part
    of the same explicit evaluator/state relation package. -/
def returnShapeRelationState : PanValueProgramState Nat :=
  { relationState with returnShapes := [("f", .one)] }

theorem panValueProgramStateRel_evalDeclarations_returnShape_adequacy_fixture
    (s' : PanValueProgramState Nat)
    (hs : evalPanValueDeclarations returnShapeRelationState relationDecls = some s')
    (hlookup : lookupInfo "f" s'.returnShapes = some .one) :
    ∃ t', evalPanValueDeclarations
        { returnShapeRelationState with
          functions := panValueFunctionsSimp returnShapeRelationState.functions }
        (panSimpDecls relationDecls) = some t' ∧
      panValueProgramStateRel s' t' ∧
      lookupInfo "f" t'.returnShapes = some .one ∧
      s'.exceptions = t'.exceptions := by
  apply panValueProgramStateRel_evalDeclarations_returnShape_adequacy
    returnShapeRelationState _
    (by
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    relationDecls none s' hs "f" .one hlookup

/-! The declaration/evaluator composition keeps a successful call argument
    value after `pan_simp` has produced the related target declaration state. -/
theorem panValueProgramStateRel_evalDeclarations_evalExp_fixture
    (s' : PanValueProgramState Nat)
    (hs : evalPanValueDeclarations relationState relationDecls = some s') :
    ∃ t', evalPanValueDeclarations
        { relationState with
          functions := panValueFunctionsSimp relationState.functions }
        (panSimpDecls relationDecls) = some t' ∧
      panValueProgramStateRel s' t' ∧
      evalPanValueExp s'.structs (fun _ => none) t'.globals
        t'.memory t'.baseAddress t'.topAddress t'.bytesInWord (.const 11) =
        some (.word 11) := by
  apply panValueProgramStateRel_evalDeclarations_evalExp relationState _
    relationState_self relationDecls none s' (.const 11) (.word 11) hs
  simp [evalPanValueExp]

/-! Regression for the function-table lookup bridge used by Cake's
    `state_rel_imp_semantics`: the entry keeps its parameters and return shape,
    while only its body is replaced by `panSimpProg`. -/
theorem lookupFunctionEntry_panSimpDecls_fixture :
    lookupFunctionEntry "f" (functions (panSimpDecls relationDecls)) =
      some ([], panSimpProg (.seq (.skip : Prog Nat) (.skip : Prog Nat)), .one) := by
  apply lookupFunctionEntry_panSimpDecls relationDecls "f"
  simp [relationDecls, functions, lookupFunctionEntry]

/-- Focused regression for `map_snd_f_eq` (`pan_simpProofScript.sml:43`):
    rewriting the body component then projecting it is the same as projecting
    it first and rewriting afterwards. -/
def bodyInc (n : Nat) : Nat := n + 10

def bodyDbl (n : Nat) : Nat := n * 2

theorem list_map_third_map_eq_fixture :
    (([("a", 1, 2), ("b", 2, 3)] : List (String × Nat × Nat)).map
        (fun t => (t.1, t.2.1, bodyInc t.2.2))).map (fun t => bodyDbl t.2.2) =
      [24, 26] := by
  rw [list_map_third_map_eq]
  decide

/-- Focused regression for the `compile_eval_correct` counterpart: expression
    evaluation is invariant under `panValueProgramStateRel`. -/
def evalRelState : PanValueProgramState Nat :=
  { structs := [], globals := fun _ => none, functions := [],
    returnShapes := [], parameterShapes := [], exceptions := [],
    memory := fun _ => none, baseAddress := 0, topAddress := 0, bytesInWord := 8 }

theorem evalPanValueExp_panValueProgramStateRel_fixture :
    evalPanValueExp ([] : StructContext) (fun _ => none) evalRelState.globals
      evalRelState.memory evalRelState.baseAddress evalRelState.topAddress
      evalRelState.bytesInWord (.const 5) = some (.word 5) :=
  evalPanValueExp_panValueProgramStateRel ([] : StructContext) (fun _ => none)
    evalRelState evalRelState
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (.const 5) none (.word 5) (by simp [evalPanValueExp])

/-- Focused regression for the `OPT_MMAP_eval_some_eq` counterpart: a whole
    expression list maps to the same values under `panValueProgramStateRel`. -/
theorem list_mapM_eval_panValueProgramStateRel_fixture :
    (([(.const 1), (.const 5)] : List (Exp Nat)).mapM (fun expression =>
      evalPanValueExp ([] : StructContext) (fun _ => none) evalRelState.globals
        evalRelState.memory evalRelState.baseAddress evalRelState.topAddress
        evalRelState.bytesInWord expression)) = some [.word 1, .word 5] :=
  list_mapM_eval_panValueProgramStateRel ([] : StructContext) (fun _ => none)
    evalRelState evalRelState
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    [.const 1, .const 5] [.word 1, .word 5] none
    (by simp [evalPanValueExp])

/-- Focused regression for the `state_rel_upd_inv` counterpart: a state
    related by `panValueProgramStateRel` is recovered by resetting the
    simplified function table. -/
theorem panValueProgramStateRel_functions_recover_fixture :
    ∃ functions,
      evalRelState =
        { { evalRelState with functions := panValueFunctionsSimp evalRelState.functions }
          with functions := functions } :=
  panValueProgramStateRel_functions_recover evalRelState
    { evalRelState with functions := panValueFunctionsSimp evalRelState.functions }
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Focused regression for the `state_rel_intro` counterpart: the related target
    state is the source state with the simplified function table. -/
theorem panValueProgramStateRel_intro_fixture :
    evalRelState =
      { evalRelState with functions := panValueFunctionsSimp evalRelState.functions } :=
  panValueProgramStateRel_intro evalRelState evalRelState
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! Regressions for Cake's `MEM_functions` (`pan_globalsProofScript.sml:2380`)
    and `evaluate_decls_functions_wf` (`:2367`). -/

/-- `MEM_functions`: the single function entry of `relationDecls` comes from the
    source function declaration. -/
theorem mem_functions_fixture :
    ∃ declaration : FunDecl Nat,
      (.function declaration : Decl Nat) ∈ relationDecls ∧
        ("f", [], (.seq (.skip : Prog Nat) (.skip : Prog Nat)), .one) =
          (declaration.name, declaration.params, declaration.body,
            declaration.returnShape) :=
  mem_functions (declarations := relationDecls)
    (entry := ("f", [], (.seq (.skip : Prog Nat) (.skip : Prog Nat)), .one))
    (by simp [relationDecls, functions])

def wfFunction : FunDecl Nat :=
  { name := "f", inline := false, exported := false, params := [],
    body := (.skip : Prog Nat), returnShape := .one }

def wfDecls : List (Decl Nat) := [.function wfFunction]

def wfEvalSucceeds : Bool :=
  (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState wfDecls
    none).isSome

#eval wfEvalSucceeds
#guard wfEvalSucceeds

/-- `evaluate_decls_functions_wf` for the struct-explicit evaluator: any function
    declaration reached by a successful evaluation is well formed. -/
theorem evalPanValueDeclarationsWithStructs_functions_wf_fixture
    (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      wfDecls none = some state') :
    isWfShape ([] : StructContext) (.one : Shape) = true :=
  (evalPanValueDeclarationsWithStructs_functions_wf ([] : StructContext) evalRelState
    state' wfDecls none heval (declaration := wfFunction) (by simp [wfDecls])).2

/-- `evaluate_decls_functions_wf` for the struct-collecting entry point. -/
theorem evalPanValueDeclarations_functions_wf_fixture
    (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState wfDecls none = some state') :
    ∃ structs : StructContext,
      collectPanValueStructs wfDecls evalRelState.structs = some structs ∧
        isWfShape structs (.one : Shape) = true := by
  obtain ⟨structs, hcollect, _hparams, hreturn⟩ :=
    evalPanValueDeclarations_functions_wf evalRelState state' wfDecls none heval
      (declaration := wfFunction) (by simp [wfDecls])
  exact ⟨structs, hcollect, hreturn⟩

/-! Regression for Cake's `evaluate_decls_exns_wf`
    (`cakeml/pancake/semantics/panPropsScript.sml:1421`): a successful
    declaration evaluation keeps every installed exception shape well formed. -/

def wfException : Decl Nat := .exnDecl "E" .one

def wfExceptionDecls : List (Decl Nat) := [wfException]

theorem evalPanValueDeclarations_exceptions_wf_fixture
    (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarationsWithStructs [] evalRelState
      wfExceptionDecls none = some state') :
    isWfShape ([] : StructContext) (.one : Shape) = true := by
  exact evalPanValueDeclarationsWithStructs_exceptions_wf [] evalRelState state'
    wfExceptionDecls none heval (exception := "E") (shape := .one) (by
      simp [wfExceptionDecls, wfException])

theorem evalPanValueDeclarations_top_exceptions_wf_fixture
    (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState wfExceptionDecls none = some state') :
    ∃ structs : StructContext,
      collectPanValueStructs wfExceptionDecls evalRelState.structs = some structs ∧
        isWfShape structs (.one : Shape) = true := by
  obtain ⟨structs, hcollect, hwf⟩ :=
    evalPanValueDeclarations_exceptions_wf evalRelState state' wfExceptionDecls none
      heval (exception := "E") (shape := .one) (by
        simp [wfExceptionDecls, wfException])
  exact ⟨structs, hcollect, hwf⟩

example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState wfExceptionDecls none = some state') :
    ∃ structs : StructContext,
      collectPanValueStructs wfExceptionDecls evalRelState.structs = some structs ∧
        state'.exceptions = panExceptionEntries wfExceptionDecls ++ evalRelState.exceptions ∧
        isWfShape structs (.one : Shape) = true := by
  exact evalPanValueDeclarations_exception_state_evidence evalRelState state'
    wfExceptionDecls none (exception := "E") (shape := .one)
    (by simp [wfExceptionDecls, wfException]) heval

/-! Regression for Cake's `evaluate_decls_append`
    (`cakeml/pancake/semantics/panPropsScript.sml:1540`): evaluating a
    concatenated declaration list is the sequential composition of evaluating
    the two parts in turn. -/

def appendDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7)]

def appendRest : List (Decl Nat) :=
  [.function wfFunction]

def appendGuard : Bool :=
  (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      (appendDecls ++ appendRest) none).isSome ==
    (match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
        appendDecls none with
     | some state' =>
         (evalPanValueDeclarationsWithStructs ([] : StructContext) state'
           appendRest none).isSome
     | none => false)

#eval appendGuard
#guard appendGuard

example : True := by
  have _h := evalPanValueDeclarationsWithStructs_append ([] : StructContext)
    evalRelState appendDecls appendRest none
  trivial

def commuteFunction : Decl Nat :=
  .function wfFunction

def commuteDecl : Decl Nat :=
  .decl .one "g" (.const 7)

def commuteGuard : Bool :=
  (match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
        [commuteFunction, commuteDecl] none,
      evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
        [commuteDecl, commuteFunction] none with
   | some left, some right =>
       (left.globals "g").isSome == (right.globals "g").isSome
   | none, none => true
   | _, _ => false)

#eval commuteGuard
#guard commuteGuard

example : True := by
  have _h := evalPanValueDeclarationsWithStructs_function_decl_commute
    ([] : StructContext) evalRelState wfFunction .one "g" (.const 7) [] none
  trivial

/-! Regression for Cake's `evaluate_decls_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1518`): a successful
    declaration evaluation only prepends the list's function entries to the
    function table. -/

def functionsDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .function wfFunction,
   .function
     { name := "h", inline := false, exported := false, params := [],
       body := (.skip : Prog Nat), returnShape := .one }]

def functionsGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      functionsDecls none with
  | some state' =>
      state'.functions.length ==
        (panFunctionEntries functionsDecls ++ evalRelState.functions).length
  | none => false

#eval functionsGuard
#guard functionsGuard

example : True := by
  cases heval : evalPanValueDeclarationsWithStructs ([] : StructContext)
      evalRelState functionsDecls none with
  | none => trivial
  | some state' =>
      have _h := evalPanValueDeclarationsWithStructs_functions ([] : StructContext)
        evalRelState state' functionsDecls none heval
      trivial

/-! Regression for Cake's `evaluate_decls_eshapes`
    (`cakeml/pancake/semantics/panPropsScript.sml:1409`): a successful
    declaration evaluation only prepends the list's exception entries to the
    exception-shape table. -/

def exceptionsDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .decl .one "g" (.const 7), .exnDecl "F" .one]

def exceptionsGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      exceptionsDecls none with
  | some state' =>
      state'.exceptions.length ==
        (panExceptionEntries exceptionsDecls ++ evalRelState.exceptions).length
  | none => false

#eval exceptionsGuard
#guard exceptionsGuard

example : True := by
  cases heval : evalPanValueDeclarationsWithStructs ([] : StructContext)
      evalRelState exceptionsDecls none with
  | none => trivial
  | some state' =>
      have _h := evalPanValueDeclarationsWithStructs_exceptions ([] : StructContext)
        evalRelState state' exceptionsDecls none heval
      trivial

/-! Regression for Cake's `evaluate_decls_only_exn_decls`: an all-exception
    declaration list changes no program component except the exception table. -/

def onlyExceptionDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .exnDecl "F" .one]

def onlyExceptionsGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      onlyExceptionDecls none with
  | some state' =>
      match state'.exceptions with
      | [("F", .one), ("E", .one)] =>
          state'.functions.isEmpty && state'.returnShapes.isEmpty &&
            Option.isNone (state'.globals "g")
      | _ => false
  | none => false

#eval onlyExceptionsGuard
#guard onlyExceptionsGuard

example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      onlyExceptionDecls none = some state') :
    state' = { evalRelState with
      exceptions := panExceptionEntries onlyExceptionDecls ++ evalRelState.exceptions } := by
  exact evalPanValueDeclarationsWithStructs_only_exn_decls ([] : StructContext)
    evalRelState state' onlyExceptionDecls none rfl (by decide) heval

/-! The public declaration evaluator preserves the same exception table after
    collecting the declaration-time struct context.  This is the direct
    state/global lookup bridge used by the top-level raised evaluator. -/
example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState exceptionsDecls none = some state') :
    state'.exceptions = panExceptionEntries exceptionsDecls ++ evalRelState.exceptions := by
  exact evalPanValueDeclarations_exceptions evalRelState state' exceptionsDecls none heval

example
    (primitive : PanPrimitiveHandler Nat) (ffi : PanValueFfiHandler Nat)
    (fuel : Nat) (entry : FunName) (arguments : List (Exp Nat))
    (memoryAccess : Option (PanValueMemoryAccess Nat))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler Nat))
    (state : PanValueProgramState Nat)
    (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (exception : ExceptionId)
    (value : PanValue Nat)
    (hdeclarations : evalPanValueDeclarations evalRelState exceptionsDecls
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram evalRelState primitive ffi fuel exceptionsDecls entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    state.exceptions = panExceptionEntries exceptionsDecls ++ evalRelState.exceptions := by
  exact evalPanValueProgram_of_declarations_and_raised_call_with_exception_state
    evalRelState primitive ffi fuel exceptionsDecls entry arguments memoryAccess
    memoryHandler state locals globals memory exception value hdeclarations hcall
example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState onlyExceptionDecls none =
      some state') :
    state' = { evalRelState with
      exceptions := panExceptionEntries onlyExceptionDecls ++ evalRelState.exceptions } := by
  exact evalPanValueDeclarations_only_exn_decls evalRelState state'
    onlyExceptionDecls none (by decide) heval

/-! Regression for Cake's `evaluate_decls_names`: structure-name
    declarations do not alter the program state during evaluation. -/

def namesOnlyDecls : List (Decl Nat) :=
  [.name "Pair" [ ("left", .one), ("right", .one) ],
   .name "Triple" [ ("a", .one), ("b", .one), ("c", .one) ]]

example :
    evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      namesOnlyDecls none = some evalRelState := by
  exact evalPanValueDeclarationsWithStructs_names ([] : StructContext)
    evalRelState namesOnlyDecls none (by decide)

/-! The public declaration evaluator preserves the same exception table after
    collecting the declaration-time struct context.  This is the direct
    state/global lookup bridge used by the top-level raised evaluator. -/
example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarations evalRelState exceptionsDecls none = some state') :
    state'.exceptions = panExceptionEntries exceptionsDecls ++ evalRelState.exceptions := by
  exact evalPanValueDeclarations_exceptions evalRelState state' exceptionsDecls none heval

example
    (primitive : PanPrimitiveHandler Nat) (ffi : PanValueFfiHandler Nat)
    (fuel : Nat) (entry : FunName) (arguments : List (Exp Nat))
    (memoryAccess : Option (PanValueMemoryAccess Nat))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler Nat))
    (state : PanValueProgramState Nat)
    (locals globals : VarName → Option (PanValue Nat))
    (memory : Nat → Option (PanValue Nat)) (exception : ExceptionId)
    (value : PanValue Nat)
    (hdeclarations : evalPanValueDeclarations evalRelState exceptionsDecls
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram evalRelState primitive ffi fuel exceptionsDecls entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    state.exceptions = panExceptionEntries exceptionsDecls ++ evalRelState.exceptions := by
  exact evalPanValueProgram_of_declarations_and_raised_call_with_exception_state
    evalRelState primitive ffi fuel exceptionsDecls entry arguments memoryAccess
    memoryHandler state locals globals memory exception value hdeclarations hcall

/-! Cake's `decs_stcnames_only_functions` / `decs_stcnames_only_functions2`
    (`cakeml/pancake/semantics/panPropsScript.sml:1592,1600`): struct-free and
    function-only declaration lists leave the struct-name context unchanged. -/

def noNameDecls : List (Decl Nat) :=
  [.function wfFunction, .exnDecl "E" .one, .decl .one "g" (.const 7)]

def functionsOnlyDecls : List (Decl Nat) := [.function wfFunction]

def functionOrExnDecls : List (Decl Nat) :=
  [.function wfFunction, .exnDecl "E" .one]

def structContextGuard : Bool :=
  (collectPanValueStructs noNameDecls ([] : StructContext)).isSome &&
    (collectPanValueStructs functionsOnlyDecls ([] : StructContext)).isSome

#eval structContextGuard
#guard structContextGuard

example : True := by
  have _h := collectPanValueStructs_of_no_names ([] : StructContext) noNameDecls
    (by decide)
  have _h2 := collectPanValueStructs_of_functions ([] : StructContext)
    functionsOnlyDecls (by decide)
  have _h3 := collectPanValueStructs_of_functions_or_exnDecls ([] : StructContext)
    functionOrExnDecls (by decide)
  trivial

#check @collectPanValueStructs_of_functions_or_exnDecls

/-! Cake's `evaluate_decls_only_exn_decls` (`panPropsScript.sml:1436`): an
    exception-only declaration list leaves every field except the
    exception-shape table unchanged. -/

def exnOnlyDecls : List (Decl Nat) := [.exnDecl "E" .one, .exnDecl "F" .one]

def exnOnlyGuard : Bool :=
  match evalPanValueDeclarations evalRelState exnOnlyDecls none with
  | some state' =>
      state'.exceptions.length ==
        (panExceptionEntries exnOnlyDecls ++ evalRelState.exceptions).length
  | none => false

#eval exnOnlyGuard
#guard exnOnlyGuard

example : True := by
  have hall : exnOnlyDecls.all isExnDecl = true := by decide
  cases heval : evalPanValueDeclarations evalRelState exnOnlyDecls none with
  | none => trivial
  | some state' =>
      have _h := evalPanValueDeclarations_only_exn_decls evalRelState state'
        exnOnlyDecls none hall heval
      trivial

/-! Cake's `evaluate_decls_only_funs_and_exn_decls`
    (`panPropsScript.sml:1561`): a list of functions and exception declarations
    leaves every other field unchanged. -/

def funsAndExnDecls : List (Decl Nat) :=
  [.function wfFunction, .exnDecl "E" .one,
   .function
     { name := "h", inline := false, exported := false, params := [],
       body := (.skip : Prog Nat), returnShape := .one },
   .exnDecl "F" .one]

def funsAndExnGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      funsAndExnDecls none with
  | some state' =>
      state'.functions.length ==
          (panFunctionEntries funsAndExnDecls ++ evalRelState.functions).length &&
        state'.returnShapes.length ==
          (panReturnShapeEntries funsAndExnDecls ++
            evalRelState.returnShapes).length &&
        state'.parameterShapes.length ==
          (panParameterShapeEntries funsAndExnDecls ++
            evalRelState.parameterShapes).length &&
        state'.exceptions.length ==
          (panExceptionEntries funsAndExnDecls ++ evalRelState.exceptions).length
  | none => false

#eval funsAndExnGuard
#guard funsAndExnGuard

example : True := by
  have hall : funsAndExnDecls.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true := by
    decide
  cases heval : evalPanValueDeclarationsWithStructs ([] : StructContext)
      evalRelState funsAndExnDecls none with
  | none => trivial
  | some state' =>
      have _h := evalPanValueDeclarationsWithStructs_only_funs_and_exn_decls
        ([] : StructContext) evalRelState state' funsAndExnDecls none rfl hall
        heval
      trivial

example (state' : PanValueProgramState Nat)
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext)
      evalRelState functionsOnlyDecls none = some state') :
    state' = { evalRelState with
      functions := panFunctionEntries functionsOnlyDecls ++ evalRelState.functions
      returnShapes :=
        panReturnShapeEntries functionsOnlyDecls ++ evalRelState.returnShapes
      parameterShapes :=
        panParameterShapeEntries functionsOnlyDecls ++ evalRelState.parameterShapes
      exceptions := evalRelState.exceptions } := by
  exact evalPanValueDeclarationsWithStructs_only_functions [] evalRelState state'
    functionsOnlyDecls none rfl (by decide) heval
/-! Cake's `evaluate_decls_only_functions` (`panPropsScript.sml:1529`): a
    function-only declaration list changes only the function table and the
    separate return-shape / parameter-shape maps. -/

def functionsOnlyStateDecls : List (Decl Nat) :=
  [.function wfFunction,
   .function
     { name := "h", inline := false, exported := false, params := [],
       body := (.skip : Prog Nat), returnShape := .one }]

def functionsOnlyStateGuard : Bool :=
  match evalPanValueDeclarations evalRelState functionsOnlyStateDecls none with
  | some state' =>
      state'.functions.length ==
          (panFunctionEntries functionsOnlyStateDecls ++
            evalRelState.functions).length &&
        state'.returnShapes.length ==
          (panReturnShapeEntries functionsOnlyStateDecls ++
            evalRelState.returnShapes).length &&
        state'.parameterShapes.length ==
          (panParameterShapeEntries functionsOnlyStateDecls ++
            evalRelState.parameterShapes).length
  | none => false

#eval functionsOnlyStateGuard
#guard functionsOnlyStateGuard

example : True := by
  have hall : functionsOnlyStateDecls.all globalDeclIsFunction = true := by
    decide
  cases heval : evalPanValueDeclarations evalRelState functionsOnlyStateDecls none with
  | none => trivial
  | some state' =>
      have _h := evalPanValueDeclarations_only_functions evalRelState state'
        functionsOnlyStateDecls none hall heval
      trivial

/-- Focused regression for the `exns_wf_evaluate_decls` counterpart: the
    distinct/no-shadowing/well-formedness conditions are sufficient for the
    evaluator to install exactly the exception table. -/
def exnsWfDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .exnDecl "F" .one]

def exnsWfGuard : Bool :=
  match evalPanValueDeclarations evalRelState exnsWfDecls none with
  | some state' =>
      state'.exceptions.length ==
        (panExceptionEntries exnsWfDecls ++ evalRelState.exceptions).length
  | none => false

#eval exnsWfGuard
#guard exnsWfGuard

example : True := by
  have hall : exnsWfDecls.all isExnDecl = true := by decide
  have hnodup : ((panExceptionEntries exnsWfDecls).map
      (fun entry => entry.1)).Nodup := by
    simp [exnsWfDecls, panExceptionEntries, exceptionEntries]
  have hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries exnsWfDecls →
        lookupInfo exception evalRelState.exceptions = none := by
    intro exception shape _
    simp [evalRelState, lookupInfo]
  have hwf : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries exnsWfDecls →
        isWfShape evalRelState.structs shape = true := by
    intro exception shape hmem
    simp [exnsWfDecls, panExceptionEntries, exceptionEntries] at hmem
    rcases hmem with h | h
    · obtain ⟨rfl, rfl⟩ := h
      simp [evalRelState, isWfShape]
    · obtain ⟨rfl, rfl⟩ := h
      simp [evalRelState, isWfShape]
  have _h := evalPanValueDeclarations_exns_wf_sufficiency evalRelState exnsWfDecls
    none hall hnodup hnone hwf
  trivial

/-- Focused regression for the `evaluate_decls_one_fun_last` counterpart: a
    trailing function declaration may be moved to the front when every
    preceding declaration is a global or exception declaration. -/
def oneFunLastDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .exnDecl "E" .one]

def oneFunLastGuard : Bool :=
  (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      (oneFunLastDecls ++ [.function wfFunction]) none).isSome ==
    (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      (.function wfFunction :: oneFunLastDecls) none).isSome

#eval oneFunLastGuard
#guard oneFunLastGuard

example : True := by
  have hrest : oneFunLastDecls.all
      (fun declaration => isDecl declaration || isExnDecl declaration) = true := by
    simp [oneFunLastDecls, isDecl, isExnDecl]
  have _h := evalPanValueDeclarationsWithStructs_one_fun_last
    ([] : StructContext) evalRelState wfFunction oneFunLastDecls none hrest
  trivial

/-- Focused regression for the `resort_decls_evaluate` counterpart: resorting
    declarations into the name/exception/global/function partition preserves
    the declaration evaluator's result. -/
def resortDeclF : Decl Nat :=
  .function { name := "f", inline := false, exported := false, params := [],
              body := (.skip : Prog Nat), returnShape := .one }

def resortDeclH : Decl Nat :=
  .function { name := "h", inline := false, exported := false, params := [],
              body := (.tick : Prog Nat), returnShape := .one }

def resortDecls : List (Decl Nat) :=
  [resortDeclF, .decl .one "g" (.const 7), .exnDecl "E" .one, resortDeclH]

def resortDeclsGuard : Bool :=
  (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      (globalResortDecls resortDecls) none).isSome ==
    (evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      resortDecls none).isSome

#eval resortDeclsGuard
#guard resortDeclsGuard

example : True := by
  have hall : resortDecls.all (fun declaration =>
      isDecl declaration || isExnDecl declaration ||
        globalDeclIsFunction declaration) = true := by
    simp [resortDecls, resortDeclF, resortDeclH, isDecl, isExnDecl,
      globalDeclIsFunction]
  have _h := evalPanValueDeclarationsWithStructs_resortDecls
    ([] : StructContext) evalRelState resortDecls none hall
  trivial

/-- `evaluate_decls_only_functions_SOME`
    (`pan_globalsProofScript.sml:2390`): a function-only declaration list with
    well-formed shapes evaluates successfully and installs exactly that table. -/
def functionsSufficiencyGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      functionsOnlyDecls none with
  | some state' =>
      state'.functions.length ==
        (panFunctionEntries functionsOnlyDecls ++
          evalRelState.functions).length
  | none => false

#eval functionsSufficiencyGuard
#guard functionsSufficiencyGuard

example : True := by
  have hall : functionsOnlyDecls.all globalDeclIsFunction = true := by
    simp [functionsOnlyDecls, globalDeclIsFunction, wfFunction]
  have _h := evalPanValueDeclarationsWithStructs_only_functions_sufficiency
    ([] : StructContext) evalRelState functionsOnlyDecls none rfl hall
    (fun declaration hmem => by
      simp [functionsOnlyDecls] at hmem
      rcases hmem with rfl
      simp [wfFunction, isWfShape])
  trivial

/-- Cake's `evaluate_decls_only_functions_and_exns_SOME`
    (`pan_globalsProofScript.sml:2404`): a mixed function/exception declaration
    list with well-formed function shapes and fresh, distinct, well-formed
    exception shapes evaluates successfully and installs exactly both tables. -/
def functionsAndExnsDecls : List (Decl Nat) :=
  [.function wfFunction, .exnDecl "E" .one, .exnDecl "F" .one]

def functionsAndExnsGuard : Bool :=
  match evalPanValueDeclarationsWithStructs ([] : StructContext) evalRelState
      functionsAndExnsDecls none with
  | some state' =>
      state'.functions.length ==
          (panFunctionEntries functionsAndExnsDecls ++
            evalRelState.functions).length &&
        state'.exceptions.length ==
          (panExceptionEntries functionsAndExnsDecls ++
            evalRelState.exceptions).length
  | none => false

#eval functionsAndExnsGuard
#guard functionsAndExnsGuard

example : True := by
  have hall : functionsAndExnsDecls.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true := by
    simp [functionsAndExnsDecls, globalDeclIsFunction, isExnDecl, wfFunction]
  have hnodup :
      ((panExceptionEntries functionsAndExnsDecls).map
        (fun entry => entry.1)).Nodup := by
    simp [functionsAndExnsDecls, panExceptionEntries, exceptionEntries]
  have hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries functionsAndExnsDecls →
        lookupInfo exception evalRelState.exceptions = none := by
    intro exception shape _
    simp [evalRelState, lookupInfo]
  have hexns : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries functionsAndExnsDecls →
        isWfShape evalRelState.structs shape = true := by
    intro exception shape hmem
    simp [functionsAndExnsDecls, panExceptionEntries, exceptionEntries] at hmem
    rcases hmem with h | h
    · obtain ⟨rfl, rfl⟩ := h
      simp [evalRelState, isWfShape]
    · obtain ⟨rfl, rfl⟩ := h
      simp [evalRelState, isWfShape]
  have _h :=
    evalPanValueDeclarationsWithStructs_only_functions_and_exns_sufficiency
      ([] : StructContext) evalRelState functionsAndExnsDecls none rfl hall
      (fun declaration hmem => by
        simp [functionsAndExnsDecls] at hmem
        rcases hmem with rfl | rfl | rfl
        all_goals simp [wfFunction, isWfShape])
      hnodup hnone hexns
  trivial

/-! Focused regression for the ported Cake `OPT_MMAP_MEM_IMP`
    (`panPropsScript.sml:115`). -/

theorem list_mapM_mem_exists_fixture :
    ∃ x, x ∈ ([3, 5] : List Nat) ∧
      (if x == 4 then none else some (x + 1)) = some 6 :=
  list_mapM_mem_exists (fun n : Nat => if n == 4 then none else some (n + 1))
    [3, 5] [4, 6] (by decide) 6 (by decide)

#check @list_mapM_mem_exists
/-! Cake's `not_mem_map_flat` (`panPropsScript.sml:1035`): absence from a
    flattened mapped list. -/

theorem not_mem_map_flatten_fixture :
    7 ∉ (([[1, 2], [3, 4]] : List (List Nat)).map id).flatten := by
  rw [not_mem_map_flatten]
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> decide

#check @not_mem_map_flatten
/-! Cake's `opt_mmap_length_eq`, `opt_mmap_mem_func` and `opt_mmap_el`
    (`pan_commonPropsScript.sml:82/49/71`): basic facts about a successful
    `OPT_MMAP`/`List.mapM`. -/

def sampleMapF (n : Nat) : Option Nat := if n % 2 == 0 then some (n + 1) else none

theorem list_mapM_length_fixture :
    ([2, 4, 6] : List Nat).length = [3, 5, 7].length :=
  list_mapM_length sampleMapF [2, 4, 6] [3, 5, 7] (by decide)

theorem list_mapM_mem_func_fixture :
    ∃ y, sampleMapF 4 = some y :=
  list_mapM_mem_func (x := 4) (xs := [2, 4, 6]) sampleMapF [3, 5, 7] (by decide) (by decide)

theorem list_mapM_getElem?_fixture :
    (([2, 4, 6] : List Nat)[1]?).bind sampleMapF = ([3, 5, 7] : List Nat)[1]? :=
  list_mapM_getElem? sampleMapF [2, 4, 6] [3, 5, 7] (by decide) 1

def mapMFactsGuard : Bool :=
  (([2, 4, 6] : List Nat).length == [3, 5, 7].length) &&
    (([2, 4, 6] : List Nat)[1]?).bind sampleMapF == ([3, 5, 7] : List Nat)[1]?

#eval mapMFactsGuard
#guard mapMFactsGuard

/-! Cake's `opt_mmap_mem_defined`, `opt_mmap_opt_map` and `map_append_eq_drop`
    (`pan_commonPropsScript.sml:59/92/39`). -/

theorem list_mapM_mem_defined_fixture :
    (3 : Nat) ∈ [3, 5, 7] :=
  list_mapM_mem_defined (x := 2) (xs := [2, 4, 6]) (e := 3) (ys := [3, 5, 7])
    sampleMapF (by decide) (by decide) (by decide)

theorem list_mapM_map_fixture :
    ([2, 4, 6] : List Nat).mapM (fun x => (sampleMapF x).map (fun y => y + 1)) =
      some [4, 6, 8] :=
  list_mapM_map sampleMapF [2, 4, 6] [3, 5, 7] (fun y => y + 1) (by decide)

theorem map_eq_append_drop_fixture :
    (([1, 2, 3, 4] : List Nat).drop 2).map (fun x => x * 2) = [6, 8] :=
  map_eq_append_drop (fun x => x * 2) [1, 2, 3, 4] [2, 4] [6, 8] (by decide)

theorem list_mapM_eq_some_map_some_fixture :
    (([2, 4, 6] : List Nat).map sampleMapF) = ([3, 5, 7] : List Nat).map some :=
  (list_mapM_eq_some_map_some sampleMapF [2, 4, 6] [3, 5, 7]).mp (by decide)

theorem optMmapEqSome_fixture :
    (([2, 4, 6] : List Nat).map sampleMapF) = ([3, 5, 7] : List Nat).map some :=
  (optMmapEqSome [2, 4, 6] sampleMapF [3, 5, 7]).mp (by decide)

theorem list_mapM_eq_some_map_some_rev_fixture :
    ([2, 4, 6] : List Nat).mapM sampleMapF = some [3, 5, 7] :=
  (list_mapM_eq_some_map_some sampleMapF [2, 4, 6] [3, 5, 7]).mpr (by decide)

#check @list_mapM_eq_some_map_some

theorem map_getD_map_some_fixture :
    ([2, 4, 6] : List Nat).map (fun x => (sampleMapF x).getD 0) = [3, 5, 7] :=
  map_getD_map_some sampleMapF 0 [2, 4, 6] [3, 5, 7] (by decide)

theorem lookup_mem_exists_fixture :
    ∃ m : Nat,
      ([("a", 10), ("b", 20)] : List (String × Nat))[m]? = some ("b", 20) :=
  lookup_mem_exists "b" [("a", 10), ("b", 20)] 20 (by decide)

#check @map_getD_map_some
#check @lookup_mem_exists

theorem map_some_getD_eq_self_fixture :
    ([1, 2, 3] : List Nat).map (fun x => (some x : Option Nat).getD 0) = [1, 2, 3] :=
  map_some_getD_eq_self 0 [1, 2, 3]

theorem mem_of_eq_mem_fixture : (2 : Nat) ∈ [1, 2, 3] :=
  mem_of_eq_mem rfl (by decide)

#check @map_some_getD_eq_self
#check @mem_of_eq_mem

def mapMoreFactsGuard : Bool :=
  (([2, 4, 6] : List Nat).mapM (fun x => (sampleMapF x).map (fun y => y + 1)) ==
      some [4, 6, 8]) &&
    ((([1, 2, 3, 4] : List Nat).drop 2).map (fun x => x * 2) == [6, 8])

#eval mapMoreFactsGuard
#guard mapMoreFactsGuard

/-! Cake's `opt_mmap_flookup_update` (`pan_commonPropsScript.sml:156`). -/

theorem list_mapM_updatePanValueMap_not_mem_fixture :
    ([2, 4, 6] : List Nat).mapM
        (fun x => updatePanValueMap sampleMapF 7 100 x) = some [3, 5, 7] :=
  list_mapM_updatePanValueMap_not_mem sampleMapF [2, 4, 6] [3, 5, 7] 7 100
    (by decide) (by decide)

def updateMapGuard : Bool :=
  ([2, 4, 6] : List Nat).mapM
      (fun x => updatePanValueMap sampleMapF 7 100 x) == some [3, 5, 7]

#eval updateMapGuard
#guard updateMapGuard

/-! Cake's `decs_stcnames_infos_ok`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:1459`): collecting the
    struct declarations preserves the `struct_infos_ok` invariant. -/

def structInfoDecls : List (Decl Nat) :=
  [.name "S" [("f", Shape.one)]]

example (context' : StructContext)
    (hcollect : collectPanValueStructs structInfoDecls ([] : StructContext) =
      some context') :
    structInfosOk context' :=
  collectPanValueStructs_structInfosOk structInfoDecls [] context' hcollect
    (by unfold structInfosOk; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp)

theorem lookupInfo_isSome_of_mem_fixture :
    (lookupInfo "S" ([("S", { fields := [("f", Shape.one)], size := 1 })]
      : StructContext)).isSome = true :=
  lookupInfo_isSome_of_mem "S"
    ([("S", { fields := [("f", Shape.one)], size := 1 })] : StructContext)
    (by simp)

#guard (lookupInfo "S" ([("S", { fields := [("f", Shape.one)], size := 1 })]
  : StructContext)).isSome

end Flapjack.Test.PanProgramSimpParity
