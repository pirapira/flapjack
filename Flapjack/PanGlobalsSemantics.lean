import Flapjack.Pancake.PanGlobals
import Flapjack.PanProgramSemantics

/-!
Supporting shape invariants for Flapjack's global compilation pass. The
HOL-mapped start-function theorems live in
this module keeps Flapjack-specific shape invariants for its own global pass.
They are not statement-shaped ports of Cake's `compile_top_shape_wf`: they use
Flapjack's value evaluator and `globalCompileTopForStart` result instead of
Cake's `evaluate_decls` and `compile_top` interfaces.
-/

namespace Flapjack

/-- Cake's shape-side condition on a function declaration
    (`EVERY (is_wf_shape s.structs ∘ SND) fi.params ∧ is_wf_shape s.structs fi.return`). -/
def panFunctionShapesWellFormed (structs : StructContext)
    (declaration : FunDecl α) : Bool :=
  declaration.params.all (fun parameter => isWfShape structs parameter.2) &&
    isWfShape structs declaration.returnShape

/-- A Flapjack declaration predicate requiring well-formed function parameter
    and return shapes; every non-function declaration satisfies it trivially.
    This represents the shape condition used by Cake's theorem, but its use in
    Flapjack-specific results below does not port that theorem's statement. -/
def panDeclShapesWellFormed (structs : StructContext)
    (declaration : Decl α) : Bool :=
  match declaration with
  | .function function => panFunctionShapesWellFormed structs function
  | _ => true

/-! Membership in a filtered list implies membership in the original list.
    (`mem_globalDeclsFilter` only reports the predicate.) -/
theorem mem_globalDeclsFilter_original {predicate : Decl α → Bool}
    {declaration : Decl α} {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (ih htail))
      · simp [hpred] at hmem
        exact List.mem_cons.mpr (Or.inr (ih hmem))

theorem globalDeclsFilter_all_of_all (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all other = true) :
    (globalDeclsFilter predicate declarations).all other = true :=
  List.all_eq_true.mpr (fun declaration hmem =>
    List.all_eq_true.mp hall declaration (mem_globalDeclsFilter_original hmem))

theorem panDeclShapesWellFormed_or_function (structs : StructContext)
    (declaration : Decl α) :
    (globalDeclIsFunction declaration ||
      panDeclShapesWellFormed structs declaration) = true := by
  cases declaration <;> simp [globalDeclIsFunction, panDeclShapesWellFormed]

/-- The renaming pass only changes a function's name and body, so the shape
    predicate is unchanged. -/
theorem panDeclShapesWellFormed_rename_update (structs : StructContext)
    (function : FunDecl α) (name : FunName) (body : Prog α) :
    panDeclShapesWellFormed structs
        (.function { function with name := name, body := body }) =
      panDeclShapesWellFormed structs (.function function) := by
  simp [panDeclShapesWellFormed, panFunctionShapesWellFormed]

theorem globalDeclsFilter_isException_all_shapes (structs : StructContext)
    (declarations : List (Decl α)) :
    (globalDeclsFilter globalDeclIsException declarations).all
      (panDeclShapesWellFormed structs) = true := by
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hpred : globalDeclIsException declaration = true := mem_globalDeclsFilter hmem
  cases declaration with
  | function function => simp [globalDeclIsException] at hpred
  | decl shape name value => simp [globalDeclIsException] at hpred
  | exnDecl exception shape => simp [panDeclShapesWellFormed]
  | name struct fields => simp [globalDeclIsException] at hpred

/-! Flapjack-specific list invariant derived from the function-shape result
    in `PanProgramSemantics`. This lifts the member-wise result to all
    declarations and supports the global compilation proof. -/
theorem evalPanValueDeclarationsWithStructs_all_shapes
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    declarations.all (panDeclShapesWellFormed structs) = true := by
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  cases declaration with
  | function function =>
      have hwf := evalPanValueDeclarationsWithStructs_functions_wf structs state
        state' declarations memoryAccess heval hmem
      simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed,
        Bool.and_eq_true] using hwf
  | decl shape name value => simp [panDeclShapesWellFormed]
  | exnDecl exception shape => simp [panDeclShapesWellFormed]
  | name struct fields => simp [panDeclShapesWellFormed]

theorem globalFindFunction_mem [BEq String] [LawfulBEq String]
    (name : FunName) (declarations : List (Decl α)) (entry : FunDecl α)
    (hfind : globalFindFunction name declarations = some entry) :
    (.function entry : Decl α) ∈ declarations := by
  induction declarations with
  | nil => simp [globalFindFunction] at hfind
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          rw [globalFindFunction.eq_def] at hfind
          by_cases hname : (function.name == name) = true
          · simp only [hname, if_pos] at hfind
            have heq : entry = function := (Option.some.inj hfind).symm
            subst heq
            exact List.mem_cons.mpr (Or.inl rfl)
          · simp only [hname] at hfind
            exact List.mem_cons.mpr (Or.inr (ih hfind))
      | decl shape name' value =>
          rw [globalFindFunction.eq_def] at hfind
          exact List.mem_cons.mpr (Or.inr (ih hfind))
      | exnDecl exception shape =>
          rw [globalFindFunction.eq_def] at hfind
          exact List.mem_cons.mpr (Or.inr (ih hfind))
      | name struct fields =>
          rw [globalFindFunction.eq_def] at hfind
          exact List.mem_cons.mpr (Or.inr (ih hfind))

theorem globalResortDecls_all_shapes (structs : StructContext)
    (declarations : List (Decl α))
    (hsource : declarations.all (panDeclShapesWellFormed structs) = true) :
    (globalResortDecls declarations).all (panDeclShapesWellFormed structs) = true := by
  simp only [globalResortDecls]
  rw [List.all_append, List.all_append, List.all_append, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact globalDeclsFilter_all_of_all globalDeclIsName
      (panDeclShapesWellFormed structs) declarations hsource
  · exact globalDeclsFilter_all_of_all globalDeclIsException
      (panDeclShapesWellFormed structs) declarations hsource
  · exact globalDeclsFilter_all_of_all globalDeclIsGlobal
      (panDeclShapesWellFormed structs) declarations hsource
  · exact globalDeclsFilter_all_of_all globalDeclIsFunction
      (panDeclShapesWellFormed structs) declarations hsource

/-- The renamed function declarations satisfy the shape predicate whenever the
    original resort list does, because renaming preserves parameter and return
    shapes. -/
theorem globalResortDecls_all_of_renamed (structs : StructContext)
    (source target : FunName) (declarations : List (Decl α))
    (hsource : (globalResortDecls declarations).all
      (panDeclShapesWellFormed structs) = true) :
    (globalResortDecls declarations).all
      (fun declaration => match declaration with
        | .function function =>
            panDeclShapesWellFormed structs (.function { function with
              name := globalRenameFunctionName source target function.name
              body := globalRenameProg source target function.body })
        | _ => true) = true := by
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hdecl := List.all_eq_true.mp hsource declaration hmem
  cases declaration with
  | function function =>
      simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed] using hdecl
  | decl shape name value => rfl
  | exnDecl exception shape => rfl
  | name struct fields => rfl

/-- Body compilation only changes a function's body, so the shape predicate is
    unchanged. -/
theorem globalRenameDecls_all_of_body_compiled [Add α] [Mul α]
    (structs : StructContext)
    (context : GlobalPassContext α) (source target : FunName)
    (declarations : List (Decl α))
    (hsource : (globalRenameDecls source target declarations).all
      (panDeclShapesWellFormed structs) = true) :
    (globalRenameDecls source target declarations).all
      (fun declaration => match declaration with
        | .function function =>
            panDeclShapesWellFormed structs (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true := by
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hdecl := List.all_eq_true.mp hsource declaration hmem
  cases declaration with
  | function function =>
      simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed] using hdecl
  | decl shape name value => rfl
  | exnDecl exception shape => rfl
  | name struct fields => rfl

/-! Internal helper showing that the compiled exception/function tables and
    synthesized entry point satisfy Flapjack's declaration-shape predicate. -/
theorem globalCompileDecs_result_shapes_wf [BEq String] [LawfulBEq String]
    [Add α] [Mul α] (structs : StructContext) (context : GlobalPassContext α)
    (declarations : List (Decl α)) (extra : Decl α)
    (hextra : panDeclShapesWellFormed structs extra = true)
    (hsource : declarations.all
      (fun declaration => match declaration with
        | .function function =>
            panDeclShapesWellFormed structs (.function { function with
              body := globalCompileProg (globalCollect context declarations)
                function.body })
        | _ => true) = true) :
    ((globalCompileDecs context declarations).exceptions ++ [extra] ++
        (globalCompileDecs context declarations).functions).all
      (panDeclShapesWellFormed structs) = true := by
  rw [globalCompileDecs_exceptions_eq_filter]
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact globalDeclsFilter_isException_all_shapes structs declarations
  · simpa using hextra
  · exact globalCompileDecs_functions_all_of_predicate context declarations
      (panDeclShapesWellFormed structs) hsource

/-- Flapjack-specific safety invariant: successful value declaration evaluation
    and successful start-function compilation yield declarations with
    well-formed function shapes. This is analogous to Cake's
    `compile_top_shape_wf` (`pan_globalsProofScript.sml:2458`), but has a
    different statement shape and evaluator/compiler interfaces; it is not a
    port of that HOL theorem. -/
theorem globalCompileTopForStart_shapes_wf
    [BEq String] [LawfulBEq String] [Add α] [Mul α]
    [BEq α] [OfNat α 0] [OfNat α 1] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (bytesInWord : α) (fromNat : Nat → α) (start : FunName)
    (compiled : List (Decl α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state')
    (hcompile : globalCompileTopForStart bytesInWord fromNat declarations start =
      some compiled) :
    compiled.all (panDeclShapesWellFormed structs) = true := by
  have hsource := evalPanValueDeclarationsWithStructs_all_shapes structs state
    state' declarations memoryAccess heval
  unfold globalCompileTopForStart at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some entry =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      have hwf := evalPanValueDeclarationsWithStructs_functions_wf structs state
        state' declarations memoryAccess heval
        (globalFindFunction_mem start declarations entry hfind)
      have hresort := globalResortDecls_all_shapes structs declarations hsource
      have hrenamed : (globalRenameDecls start (globalNewMainName declarations)
          (globalResortDecls declarations)).all
          (panDeclShapesWellFormed structs) = true :=
        globalRenameDecls_all_of_predicate start (globalNewMainName declarations)
          (panDeclShapesWellFormed structs) (globalResortDecls declarations)
          (List.all_eq_true.mpr
            (fun declaration _ => panDeclShapesWellFormed_or_function structs declaration))
          (globalResortDecls_all_of_renamed structs start
            (globalNewMainName declarations) declarations hresort)
      refine globalCompileDecs_result_shapes_wf structs _ _ _ ?_ ?_
      · simp [panDeclShapesWellFormed, panFunctionShapesWellFormed, hwf.1, hwf.2]
      · simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed] using hrenamed

/-- Empty-struct-context instance of Flapjack's start-function shape invariant.
    This analogously specializes Cake's `compile_top_shape_wf_nil`
    (`pan_globalsProofScript.sml:2495`), but is not that theorem's HOL-shaped
    statement. -/
theorem globalCompileTopForStart_shapes_wf_nil
    [BEq String] [LawfulBEq String] [Add α] [Mul α]
    [BEq α] [OfNat α 0] [OfNat α 1] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (bytesInWord : α) (fromNat : Nat → α) (start : FunName)
    (compiled : List (Decl α))
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) state
      declarations memoryAccess = some state')
    (hcompile : globalCompileTopForStart bytesInWord fromNat declarations start =
      some compiled) :
    compiled.all (panDeclShapesWellFormed ([] : StructContext)) = true :=
  globalCompileTopForStart_shapes_wf ([] : StructContext) state state'
    declarations memoryAccess bytesInWord fromNat start compiled heval hcompile

end Flapjack
