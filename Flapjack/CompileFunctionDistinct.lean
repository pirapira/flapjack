import Flapjack.Pancake.PanToCrep.Compile

/-!
# Function-name invariants for the Pancake-to-Crep compiler

CakeML's `pan_to_crep` correctness development keeps the compiled function
table keyed by distinct names.  `compileFunctionsSource` filters non-function
declarations while preserving each function declaration's name, so the
invariant is a direct but useful bridge between a source declaration list and
the table consumed by call correctness.
-/

namespace Flapjack

def functionDeclarationNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      declaration.name :: functionDeclarationNames declarations
  | _ :: declarations => functionDeclarationNames declarations
termination_by declarations => sizeOf declarations

/-! The source function list underlying Cake's `functions` projection.  Keeping
    the declaration itself, rather than only its name, makes the indexed
    provenance of `compile_to_crep` explicit. -/
def functionDeclarations : List (Decl α) → List (FunDecl α)
  | [] => []
  | .function declaration :: declarations =>
      declaration :: functionDeclarations declarations
  | _ :: declarations => functionDeclarations declarations
termination_by declarations => sizeOf declarations

/- The source-shaped `compileToCrep` uses `compileFunctionsSource` and preserves the same
   declaration-name projection.  This is the name-distinctness premise needed
   by the complete `compile_prog`/inline boundary. -/
theorem compileFunctionsSource_map_name
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    (compileFunctionsSource context declarations).map CompiledFunction.name =
      functionDeclarationNames declarations := by
  induction declarations with
  | nil => simp [compileFunctionsSource, functionDeclarationNames]
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          simp [compileFunctionsSource, functionDeclarationNames, ih,
            compileFunDeclSource]
      | decl shape declaration value =>
          simpa [compileFunctionsSource, functionDeclarationNames] using ih
      | exnDecl exception shape =>
          simpa [compileFunctionsSource, functionDeclarationNames] using ih
      | name struct fields =>
          simpa [compileFunctionsSource, functionDeclarationNames] using ih

/-! Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_to_crepProofScript.sml:4589-4601`) for the source-shaped compiler.
    `compileFunctionsSource` filters non-function declarations, so the
    function declaration at an index and the compiled function at that index
    remain paired.  This is the indexed table-provenance fact needed before
    lifting source state semantics through `compile_to_crep`. -/
theorem compileFunctionsSource_getElem?_origin
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    {n : Nat} {function : CompiledFunction α}
    (hcompiled : (compileFunctionsSource context declarations)[n]? = some function) :
    ∃ declaration : FunDecl α,
      (functionDeclarations declarations)[n]? = some declaration ∧
      function = compileFunDeclSource context declaration := by
  induction declarations generalizing n function with
  | nil =>
      simp [compileFunctionsSource] at hcompiled
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          cases n with
          | zero =>
              simp only [compileFunctionsSource, List.getElem?_cons_zero] at hcompiled
              simp only [Option.some.injEq] at hcompiled
              subst function
              exact ⟨declaration, by simp [functionDeclarations], rfl⟩
          | succ n =>
              have htail :
                  (compileFunctionsSource context declarations)[n]? = some function := by
                simpa [compileFunctionsSource] using hcompiled
              obtain ⟨found, hfound, horigin⟩ := ih htail
              exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | decl shape name value =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | exnDecl exception shape =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | name struct fields =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩

/-! The same indexed provenance at the public `compileToCrep` boundary. -/
theorem compileToCrep_getElem?_origin
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    {n : Nat} {function : CompiledFunction α}
    (hcompiled : (compileToCrep context declarations)[n]? = some function) :
    ∃ declaration : FunDecl α,
      (functionDeclarations declarations)[n]? = some declaration ∧
      function = compileFunDeclSource
        { context with functions := functionInfos declarations } declaration := by
  apply compileFunctionsSource_getElem?_origin
    ({ context with functions := functionInfos declarations }) declarations
  simpa [compileToCrep] using hcompiled

theorem compileToCrep_names_nodup
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : (functionDeclarationNames declarations).Nodup) :
    (compileToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  rw [compileToCrep]
  rw [compileFunctionsSource_map_name]
  exact hnodup

/-! The HOL theorem `first_compile_to_crep_all_distinct` is stated over the
    source function projection, rather than over the declaration-list helper
    used by the recursive compiler proof above.  Keep that source-facing
    statement explicit so callers porting the original correctness proof do
    not need to unfold the declaration filter themselves. -/
theorem functionDeclarationNames_eq_functionDeclarations_map_name
    (declarations : List (Decl α)) :
    functionDeclarationNames declarations =
      (functionDeclarations declarations).map (fun declaration => declaration.name) := by
  induction declarations with
  | nil => simp [functionDeclarationNames, functionDeclarations]
  | cons declaration declarations ih =>
      cases declaration <;> simp [functionDeclarationNames, functionDeclarations, ih]

theorem compileToCrep_names_nodup_of_functionDeclarations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : ((functionDeclarations declarations).map
      (fun declaration => declaration.name)).Nodup) :
    (compileToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  apply compileToCrep_names_nodup context declarations
  simpa [functionDeclarationNames_eq_functionDeclarations_map_name] using hnodup

/- Cake's `compile_prog_distinct_params` theorem states that every compiled
   function has distinct flattened parameter slots.  The source-faithful
   `compileToCrep` boundary exposes those slots as `List.range`, so this
   invariant is independent of function-body lowering. -/
theorem compileFunctionsSource_params_nodup
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    ∀ function ∈ compileFunctionsSource context declarations,
      function.params.Nodup := by
  induction declarations with
  | nil => simp [compileFunctionsSource]
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          intro function hfunction
          simp only [compileFunctionsSource, List.mem_cons] at hfunction
          rcases hfunction with rfl | hfunction
          · simp [compileFunDeclSource, panToCrepVars_eq, List.nodup_range]
          · exact ih function hfunction
      | decl shape name value =>
          simpa [compileFunctionsSource] using ih
      | exnDecl exception shape =>
          simpa [compileFunctionsSource] using ih
      | name struct fields =>
          simpa [compileFunctionsSource] using ih

theorem compileToCrep_params_nodup
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    ∀ function ∈ compileToCrep context declarations,
      function.params.Nodup := by
  simpa [compileToCrep] using
    compileFunctionsSource_params_nodup
      ({ context with functions := functionInfos declarations } : CompileContext α)
      declarations

end Flapjack
