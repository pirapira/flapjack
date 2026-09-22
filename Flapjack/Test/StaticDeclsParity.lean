import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `static_check_decls_def`
    (`cakeml/pancake/panStaticScript.sml:1820-1942`). -/

def staticDeclsContext : StaticDeclContext :=
  { functions := []
    globals := []
    exceptions := [] }

def staticDeclsCheck (declarations : List (Decl Nat)) :
    StaticResult StaticDeclContext :=
  staticCheckDecls ([] : StructContext) staticDeclsContext declarations

def staticDeclsFunction (name : String) (exported : Bool)
    (params : List (VarName × Shape)) (returnShape : Shape) : Decl Nat :=
  .function
    { name := name
      inline := false
      exported := exported
      params := params
      body := .skip
      returnShape := returnShape }

def staticDeclsWarnings (declarations : List (Decl Nat)) : List String :=
  (staticDeclsCheck declarations).2.map statErrMessage

#guard
  staticDeclsWarnings
      [.decl .one "g" (.const 0), .decl .one "g" (.const 1)] ==
    ["variable g is redeclared in top-level declaration\n"]

#guard
  staticResultErrorMessage
      (staticDeclsCheck [.decl (.comb [.one, .one]) "g" (.const 0)]) ==
    some "expression to initialise global variable g has shape 1 instead of declared shape {1,1} in initialisation of global variable g\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [.decl (.named "Missing") "g" (.const 0)]) ==
    some "struct name Missing is not in scope in initialisation of global variable g\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [staticDeclsFunction "main" false [] (.comb [.one, .one])]) ==
    some "main function return has shape {1,1} instead of a word in function main\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [staticDeclsFunction "main" false [("arg", .one)] .one]) ==
    some "main function has arguments\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [staticDeclsFunction "main" true [] .one]) ==
    some "main function is exported\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [staticDeclsFunction "exported" true [] (.comb [.one, .one])]) ==
    some "exported function return has shape {1,1} instead of a word in function exported\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck
        [staticDeclsFunction "f" false [("z", .one), ("z", .one)] .one]) ==
    some "parameter z is redeclared in function f\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck
        [staticDeclsFunction "f" true
          [("a", .one), ("b", .one), ("c", .one), ("d", .one), ("e", .one)] .one]) ==
    some "exported function f has more than 4 arguments\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck
        [staticDeclsFunction "f" false [] .one,
          staticDeclsFunction "f" false [] .one]) ==
    some "function f is redeclared in top-level declaration\n"

#guard
  staticResultErrorMessage
      (staticDeclsCheck [.exnDecl "E" .one, .exnDecl "E" .one]) ==
    some "exception E is redeclared\n"

end Flapjack
