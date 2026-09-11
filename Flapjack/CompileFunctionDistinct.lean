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

end Flapjack
