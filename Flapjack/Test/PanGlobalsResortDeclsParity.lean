import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanGlobalsResortDeclsParity

/-! Direct parity for `pan_globals$resort_decls_def`
    (`pan_globalsScript.sml:179`). -/
def parityGuard : Bool :=
  (match globalResortDecls
      [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one] with
  | [.name "S" [], .exnDecl "E" .one, .decl .one "g" (.const 7)] => true
  | _ => false) &&
  (match globalResortDecls
      [.name "S1" [], .name "S2" [], .exnDecl "E1" .one,
       .exnDecl "E2" .one, .decl .one "g1" (.const 1),
       .decl .one "g2" (.const 2)] with
  | [.name "S1" [], .name "S2" [], .exnDecl "E1" .one,
     .exnDecl "E2" .one, .decl .one "g1" (.const 1),
     .decl .one "g2" (.const 2)] => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-- Replays the `empty` direct-HOL row (`resort_decls [] = []`). -/
def emptyGuard : Bool :=
  (globalResortDecls ([] : List (Decl Nat))).isEmpty

#eval emptyGuard
#guard emptyGuard

def runChecks : IO Bool := do
  IO.println (if parityGuard && emptyGuard then
    "PASS pan_globals resort_decls_def parity (3 HOL rows)"
    else "FAIL pan_globals resort_decls_def parity (3 HOL rows)")
  pure (parityGuard && emptyGuard)

end Flapjack.Test.PanGlobalsResortDeclsParity
