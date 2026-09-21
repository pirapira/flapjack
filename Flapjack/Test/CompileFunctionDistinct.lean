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

/-! The indexed source/compiled pairing used by Cake's
    `el_compile_prog_el_prog_eq`: the first compiled function is sourced from
    the first function declaration, even when exception/global declarations
    precede it. -/
theorem distinctFunctionDeclarations_first_compiled_origin :
    ∃ declaration function,
      (functionDeclarations distinctFunctionDeclarations)[0]? = some declaration ∧
      (compileFunctionsSource distinctCompileContext distinctFunctionDeclarations)[0]? =
        some function ∧
      function = compileFunDeclSource distinctCompileContext declaration := by
  have hcompiled :
      ∃ function,
        (compileFunctionsSource distinctCompileContext distinctFunctionDeclarations)[0]? =
          some function := by
    simp [compileFunctionsSource, distinctFunctionDeclarations]
  obtain ⟨function, hcompiled⟩ := hcompiled
  obtain ⟨declaration, hsource, horigin⟩ :=
    compileFunctionsSource_getElem?_origin distinctCompileContext
      distinctFunctionDeclarations hcompiled
  exact ⟨declaration, function, hsource, hcompiled, horigin⟩

#guard
    (functionDeclarationNames duplicateFunctionDeclarations) = ["same", "same"]

#guard
    (compileToCrepe distinctCompileContext distinctFunctionDeclarations).map
      CompiledFunction.name = ["first", "second"]

#guard
    (compileToCrep distinctCompileContext distinctFunctionDeclarations).map
      CompiledFunction.params = [[0, 1, 2], []]

#guard
    (functionDeclarations distinctFunctionDeclarations).length = 2

end Flapjack
