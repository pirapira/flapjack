import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `static_check_progs_def`
    (`cakeml/pancake/panStaticScript.sml:1766-1817`). -/

def staticProgsContext : StaticDeclContext :=
  { functions := [("f", { returnShape := .one, params := [] })]
    globals := []
    exceptions := [] }

def staticProgsFunction (body : Prog Nat) (params : List (VarName × Shape)) : Decl Nat :=
  .function
    { name := "f"
      inline := false
      exported := false
      params := params
      body := body
      returnShape := .one }

#guard
  staticResultErrorMessage
      (staticCheckProgs ([] : StructContext) staticProgsContext
        [staticProgsFunction .skip []]) ==
    some "branches missing return statement in function f\n"

#guard
  staticResultOk
      (staticCheckProgs ([] : StructContext) staticProgsContext
        [staticProgsFunction (.return (.const 7)) []])

#guard
  staticResultErrorMessage
      (staticCheckProgs ([] : StructContext) staticProgsContext
        [staticProgsFunction .skip [("p", .named "Missing")]]) ==
    some ("static analysis failed to convert in-scope shape in function f\n" ++
      "this should never happen. please report to a compiler developer\n")

end Flapjack
