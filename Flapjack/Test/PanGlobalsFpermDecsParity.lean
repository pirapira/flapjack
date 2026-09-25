import Flapjack.Pancake.Proofs.PanGlobals

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

def singletonNonFunctionDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7)]

theorem fpermDecsDeclsSingletonFixture :
    globalRenameDecls "foo" "bar" singletonNonFunctionDecls =
      singletonNonFunctionDecls :=
  fperm_decs_decls "foo" "bar" singletonNonFunctionDecls [] (by decide)

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

def emptyGuard : Bool :=
  (globalRenameDecls "foo" "bar" ([] : List (Decl Nat))).isEmpty

#guard emptyGuard

def singletonGuard : Bool :=
  match globalRenameDecls "foo" "bar" singletonNonFunctionDecls with
  | [.decl .one "g" (.const 7)] => true
  | _ => false

#guard singletonGuard

def runChecks : IO Bool := do
  IO.println (if parityGuard && emptyGuard && singletonGuard then
    "PASS pan_globals fperm_decs_def / fperm_decs_decls parity (3 HOL rows)"
    else "FAIL pan_globals fperm_decs_def / fperm_decs_decls parity (3 HOL rows)")
  pure (parityGuard && emptyGuard && singletonGuard)

end Flapjack.Test.PanGlobalsFpermDecsParity
