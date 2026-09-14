import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsDecShapesParity

/-! Direct parity for `pan_globals$dec_shapes_def`
    (`pan_globalsScript.sml:228`). -/
def parityGuard : Bool :=
  let empty := globalDeclShapes ([] : List (Decl Nat))
  let mixed :=
    globalDeclShapes
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one },
       .decl (.comb [.one, .named "S"]) "g" (.const 7),
       .name "S" [], .exnDecl "E" (.named "T"),
       .decl .one "h" (.const 9)]
  (match empty with
  | [] => true
  | _ => false) &&
  (match mixed with
  | [.comb [.one, .named "S"], .one] => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsDecShapesParity
