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

/-! Counterparts of Cake's `dec_shapes` cluster
    (`pan_globalsProofScript.sml:2328-2361`), exercised on the same fixture. -/
def clusterGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .decl (.comb [.one, .named "S"]) "g" (.const 7),
     .name "S" [], .exnDecl "E" (.named "T"),
     .decl .one "h" (.const 9)]
  let rest : List (Decl Nat) := [.decl .one "k" (.const 11)]
  (match globalDeclShapes (declarations ++ rest) with
   | [.comb [.one, .named "S"], .one, .one] => true
   | _ => false) &&
  (match globalDeclShapes
      (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration) declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsFunction declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsName declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsException declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsGlobal declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes (globalResortDecls declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false)

#eval clusterGuard
#guard clusterGuard

end Flapjack.Test.PanGlobalsDecShapesParity
