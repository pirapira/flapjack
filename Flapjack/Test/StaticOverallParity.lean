import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `static_check_def`
    (`cakeml/pancake/panStaticScript.sml:1983-1997`).  The guards exercise the
    complete names -> declarations -> function-bodies composition rather than
    calling one checker stage in isolation. -/

def staticOverallFunction (body : Prog Nat) : Decl Nat :=
  .function
    { name := "main"
      inline := false
      exported := false
      params := []
      body := body
      returnShape := .one }

#guard staticResultOk
  (staticCheck [staticOverallFunction (.return (.const 0))])

#guard
  staticResultErrorMessage
      (staticCheck (α := Nat) [
        .name "Pair" [("left", .one)],
        .name "Pair" [("left", .one)]]) ==
    some "struct name Pair is redeclared in top-level declaration\n"

#guard
  staticResultErrorMessage
      (staticCheck [staticOverallFunction .skip]) ==
    some "branches missing return statement in function main\n"

#guard
  staticResultErrorMessage
      (staticCheck [.decl (.comb [.one, .one]) "g" (.const 0)]) ==
    some "expression to initialise global variable g has shape 1 instead of declared shape {1,1} in initialisation of global variable g\n"

end Flapjack
