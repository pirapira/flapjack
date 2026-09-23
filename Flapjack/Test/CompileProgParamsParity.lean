import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams

namespace Flapjack.Test.CompileProgParamsParity

open Flapjack

/-! Direct `params_two_words` result from the original HOL
    `compile_prog_probe.out`: the structured parameter occupies slots 0, 1. -/
def twoWordParamDecls : List (Decl (BitVec 8)) :=
  [.function
     { name := "pair", inline := false, exported := false,
       params := [("p", .comb [.one, .one])],
       body := .skip, returnShape := .one }]

def twoWordParamParity : Bool :=
  match compileProgTopHOL twoWordParamDecls with
  | [("pair", [0, 1], .skip)] => true
  | _ => false

#guard twoWordParamParity

theorem twoWordParamNodup :
    ∀ function ∈ compileProgTopHOL twoWordParamDecls,
      function.2.1.Nodup :=
  compileProgTopHOL_params_nodup twoWordParamDecls

end Flapjack.Test.CompileProgParamsParity
