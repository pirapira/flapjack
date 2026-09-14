import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsFpermDecsParity

/-! Direct parity for `pan_globals$fperm_decs_def`
    (`pan_globalsScript.sml:216`). -/
def sourceFunction : FunDecl Nat :=
  { name := "foo"
    inline := false
    exported := true
    params := []
    body := .call none "foo" []
    returnShape := .one }

def targetFunction : FunDecl Nat :=
  { name := "bar"
    inline := true
    exported := false
    params := []
    body := .decCall "x" .one "foo" [] .skip
    returnShape := .one }

def parityGuard : Bool :=
  let renamed :=
    globalRenameDecls "foo" "bar"
      ([.decl .one "g" (.const 7), .function sourceFunction,
        .function targetFunction] : List (Decl Nat))
  match renamed with
  | [.decl .one "g" (.const 7), .function first, .function second] =>
      first.name == "bar" &&
      (match first.body with
      | .call none "bar" [] => true
      | _ => false) &&
      second.name == "foo" &&
      (match second.body with
      | .decCall "x" .one "bar" [] .skip => true
      | _ => false) &&
      first.inline == false && first.exported == true &&
      second.inline == true && second.exported == false
  | _ => false

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsFpermDecsParity
