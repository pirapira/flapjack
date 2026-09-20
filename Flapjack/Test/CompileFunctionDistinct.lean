import Flapjack.CompileFunctionDistinct

namespace Flapjack

def distinctFunctionDeclarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "first", inline := false, exported := false,
       params := [("argument", .comb [.one, .one]), ("flag", .one)],
       body := .skip, returnShape := .one },
   .decl .one "global" (.const 0),
   .function
     { name := "second", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

def duplicateFunctionDeclarations : List (Decl Nat) :=
  [.function
     { name := "same", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one },
   .function
     { name := "same", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

def distinctCompileContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

theorem distinctFunctionDeclarations_names_nodup :
    (functionDeclarationNames distinctFunctionDeclarations).Nodup := by
  simp [distinctFunctionDeclarations, functionDeclarationNames]

theorem distinctFunctionDeclarations_compiled_names_nodup :
    (compileToCrepe distinctCompileContext distinctFunctionDeclarations).map
      CompiledFunction.name |>.Nodup := by
  exact compileToCrepe_names_nodup _ _
    distinctFunctionDeclarations_names_nodup

theorem distinctFunctionDeclarations_compiled_params_nodup :
    ∀ function ∈ compileToCrep distinctCompileContext distinctFunctionDeclarations,
      function.params.Nodup := by
  exact compileToCrep_params_nodup _ _

#guard
    (functionDeclarationNames duplicateFunctionDeclarations) = ["same", "same"]

#guard
    (compileToCrepe distinctCompileContext distinctFunctionDeclarations).map
      CompiledFunction.name = ["first", "second"]

#guard
    (compileToCrep distinctCompileContext distinctFunctionDeclarations).map
      CompiledFunction.params = [[0, 1, 2], []]

end Flapjack
