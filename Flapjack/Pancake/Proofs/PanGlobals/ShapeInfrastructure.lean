import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.Semantics.PanSem

/-!
Shape infrastructure for the global pass. The relation between a successful
declaration evaluation and well-formed function shapes is proved over the
faithful `panSem$evaluate_decls` port (`evaluateDecls`), as the tagged
`evaluate_decls_functions_wf` port. The remaining predicates and helper lemmas
describe Flapjack's own `isWfShape` bookkeeping and list/filter support; they
are Flapjack-specific infrastructure with no separate HOL theorem, and none
claims a direct HOL correspondence. The full HOL `compile_top_shape_wf` and
its `compile_top_shape_wf_nil` corollary are proved in
`Flapjack/Pancake/Proofs/PanGlobals.lean`.
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
/-- Flapjack-specific filter support: membership in its filtered list implies
    membership in the original list. This generic fact has no separate HOL
    theorem declaration. -/
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

/-- Flapjack-specific list-filter support; no separate HOL theorem is ported. -/
theorem globalDeclsFilter_all_of_all (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all other = true) :
    (globalDeclsFilter predicate declarations).all other = true :=
  List.all_eq_true.mpr (fun declaration hmem =>
    List.all_eq_true.mp hall declaration (mem_globalDeclsFilter_original hmem))

/-- Flapjack-specific predicate support; this is not a Cake theorem port. -/
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

/-- Flapjack-specific support for the exception branch of its shape predicate;
    it has no separate HOL theorem declaration. -/
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

/-- Flapjack-only infrastructure analogue of Cake's `evaluate_decls_functions_wf`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2367`): a successful
    declaration evaluation only installs function declarations whose parameter
    and return shapes are well formed in the source struct context. The
    admissibility premise `panSemCompileTopAdmissible` is the constructor form
    of HOL's `EVERY (\d. is_function d ∨ is_decl d ∨ is_exn_decl d) code`.

    Not an exact HOL port: the HOL declaration is `[local]` (not exported by
    `pan_globalsProof`) and is stated over the exact `panSem$evaluate_decls`
    together with the exact `panLang$decl`/shape carriers, whereas this Lean
    theorem reads the production `PanSemDeclarationState`/`Decl`/`isWfShape`
    String/Shape carriers. The `@[hol]` tag was withdrawn (bead
    `flapjack-4ac.7`); the public consequence `evaluate_decls_functions` is the
    exact port and is integrated as
    `evaluateDeclsHOLFinite_functions`. -/
theorem evaluateDeclsFunctionsWf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String]
    (state : PanSemDeclarationState α σ) (declarations : List (Decl α))
    (state' : PanSemDeclarationState α σ)
    {function : FunDecl α}
    (heval : evaluateDecls state declarations = some state')
    (hmem : (.function function : Decl α) ∈ declarations)
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    function.params.all (fun parameter =>
      isWfShape state.runtime.structs parameter.2) = true ∧
      isWfShape state.runtime.structs function.returnShape = true := by
  induction declarations generalizing state state' with
  | nil => cases hmem
  | cons head tail ih =>
      have hadmissibleTail : tail.all panSemCompileTopAdmissible = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hadmissible
        exact hadmissible.2
      cases head with
      | name name fields =>
          simp only [evaluateDecls] at heval
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · exact ih state state' heval htail hadmissibleTail
      | decl shape name expression =>
          simp only [evaluateDecls] at heval
          cases hevalExp : evalPanValueExp state.runtime.structs (fun _ => none)
              state.runtime.globals state.runtime.memory state.runtime.baseAddress
              state.runtime.topAddress state.runtime.bytesInWord expression
              (memoryAccess := some state.memoryAccess) with
          | none => simp [hevalExp] at heval
          | some value =>
              cases hshape : panShapeMatches
                  (panValueShape state.runtime.structs value) shape with
              | false => simp [hevalExp, hshape] at heval
              | true =>
                simp [hevalExp, hshape] at heval
                rcases List.mem_cons.mp hmem with hhead | htail
                · cases hhead
                · exact ih
                    { state with runtime :=
                      { state.runtime with globals :=
                        panSemDeclUpdateGlobal state.runtime.globals name value } }
                    state' heval htail hadmissibleTail
      | function current =>
          simp only [evaluateDecls] at heval
          cases hwf : (current.params.all (fun parameter =>
              isWfShape state.runtime.structs parameter.2) &&
              isWfShape state.runtime.structs current.returnShape) with
          | false => simp [hwf] at heval
          | true =>
            simp [hwf] at heval
            rcases List.mem_cons.mp hmem with hhead | htail
            · have hsame : function = current := by
                injection hhead
              subst current
              simpa only [Bool.and_eq_true] using hwf
            · let entry : PanSemFunctionEntry α :=
                { params := current.params
                  body := current.body
                  returnShape := current.returnShape }
              let nextState : PanSemDeclarationState α σ :=
                { state with code :=
                  panSemDeclUpdateInfo state.code current.name entry }
              exact ih nextState state' heval htail hadmissibleTail
      | exnDecl exception shape =>
          simp only [evaluateDecls] at heval
          cases hduplicate : (lookupInfo exception state.eshapes).isSome with
          | true => simp [hduplicate] at heval
          | false =>
            cases hwf : isWfShape state.runtime.structs shape with
            | false => simp [hduplicate, hwf] at heval
            | true =>
              simp [hduplicate, hwf] at heval
              rcases List.mem_cons.mp hmem with hhead | htail
              · cases hhead
              · exact ih
                  { state with eshapes :=
                    panSemDeclUpdateInfo state.eshapes exception shape }
                  state' heval htail hadmissibleTail

/-- Flapjack-specific lookup support; this representation-specific fact has
    no separate HOL theorem declaration. -/
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

/-- Flapjack-specific shape-filter invariant used by the open global-pass
    proof; it is not a port of a HOL theorem. -/
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
    (hsource : ∀ context, declarations.all
      (fun declaration => match declaration with
        | .function function =>
            panDeclShapesWellFormed structs (.function { function with
              body := globalCompileProg context function.body })
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

end Flapjack
