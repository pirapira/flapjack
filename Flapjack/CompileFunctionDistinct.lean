import Flapjack.Compile

/-!
# Function-name invariants for the Pancake-to-Crep compiler

CakeML's `pan_to_crep` correctness development keeps the compiled function
table keyed by distinct names.  `compileFunctions` filters non-function
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

theorem compileFunctions_map_name
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    (compileFunctions context declarations).map CompiledFunction.name =
      functionDeclarationNames declarations := by
  induction declarations with
  | nil => simp [compileFunctions, functionDeclarationNames]
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          simp [compileFunctions, functionDeclarationNames, ih, compileFunDecl]
      | decl shape declaration value =>
          simpa [compileFunctions, functionDeclarationNames] using ih
      | exnDecl exception shape =>
          simpa [compileFunctions, functionDeclarationNames] using ih
      | name struct fields =>
          simpa [compileFunctions, functionDeclarationNames] using ih

theorem compileFunctions_names_nodup
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (names : List FunName)
    (hnames : functionDeclarationNames declarations = names)
    (hnodup : names.Nodup) :
    (compileFunctions context declarations).map CompiledFunction.name |>.Nodup := by
  rw [compileFunctions_map_name context declarations, hnames]
  exact hnodup

theorem compileToCrepe_names_nodup
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : (functionDeclarationNames declarations).Nodup) :
    (compileToCrepe context declarations).map CompiledFunction.name |>.Nodup := by
  simpa [compileToCrepe] using
    (compileFunctions_names_nodup
      ({ context with functions := functionInfos declarations }) declarations
      (functionDeclarationNames declarations) rfl hnodup)

/- The source-shaped `compileToCrep` uses `compileFunctionsSource` rather
   than the context-normalized table above, but it preserves the same
   declaration-name projection.  This is the name-distinctness premise needed
   by the complete `compile_prog`/inline boundary. -/
theorem compileFunctionsSource_map_name
    [BEq α] [OfNat α 0] [Add α]
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

theorem compileToCrep_names_nodup
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : (functionDeclarationNames declarations).Nodup) :
    (compileToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  rw [compileToCrep]
  rw [compileFunctionsSource_map_name]
  exact hnodup

/- Cake's `compile_prog_distinct_params` theorem states that every compiled
   function has distinct flattened parameter slots.  The source-faithful
   `compileToCrep` boundary exposes those slots as `List.range`, so this
   invariant is independent of function-body lowering. -/
theorem compileFunctionsSource_params_nodup
    [BEq α] [OfNat α 0] [Add α]
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
          · simp [compileFunDeclSource, panToCrepVars, List.nodup_range]
          · exact ih function hfunction
      | decl shape name value =>
          simpa [compileFunctionsSource] using ih
      | exnDecl exception shape =>
          simpa [compileFunctionsSource] using ih
      | name struct fields =>
          simpa [compileFunctionsSource] using ih

theorem compileToCrep_params_nodup
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    ∀ function ∈ compileToCrep context declarations,
      function.params.Nodup := by
  simpa [compileToCrep] using
    compileFunctionsSource_params_nodup
      ({ context with functions := functionInfos declarations } : CompileContext α)
      declarations

end Flapjack
