import Flapjack.PanProgramSimp

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

end Flapjack.Test.PanProgramSimpParity
