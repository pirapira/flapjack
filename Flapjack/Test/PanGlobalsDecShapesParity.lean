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

/-! Counterpart of Cake's `exceptions_append`
    (`pan_globalsProofScript.sml:2507`), exercised on a mixed fixture. -/
def exceptionEntriesGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T")]
  let rest : List (Decl Nat) := [.exnDecl "F" .one, .decl .one "k" (.const 11)]
  (match exceptionEntries (declarations ++ rest) with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false) &&
  (match exceptionEntries declarations ++ exceptionEntries rest with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false)

#eval exceptionEntriesGuard
#guard exceptionEntriesGuard

/-! Counterpart of Cake's `exceptions_FILTER_is_function`
    (`pan_globalsProofScript.sml:2515`), exercised on a mixed fixture. -/
def exceptionEntriesFilterGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"),
     .decl .one "h" (.const 9)]
  (match exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) with
   | [] => true
   | _ => false) &&
  (match exceptionEntries
      (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations) with
   | [("E", .named "T")] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsException declarations) with
   | [("E", .named "T")] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsName declarations) with
   | [] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsGlobal declarations) with
   | [] => true
   | _ => false)

#eval exceptionEntriesFilterGuard
#guard exceptionEntriesFilterGuard

end Flapjack.Test.PanGlobalsDecShapesParity
