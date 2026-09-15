import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileDecsParity

def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-! Direct parity for `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:160`). -/
def parityGuard : Bool :=
  (match globalCompileDecs compileContext [] with
  | { initializers := [], functions := [], exceptions := [], context :=
      { globals := [], globalsSize := 1, maxGlobalsSize := 16,
        bytesInWord := 1, fromNat := _ } } => true
  | _ => false) &&
  (match globalCompileDecs compileContext
      [.decl .one "g" (.const 7)] with
  | { initializers :=
      [.store (.op .sub [.topAddr, .const 2]) (.const 7)],
      functions := [], exceptions := [], context :=
      { globals := [("g", (.one, 2))], globalsSize := 2,
        maxGlobalsSize := 16, bytesInWord := 1, fromNat := _ } } => true
  | _ => false) &&
  (match globalCompileDecs compileContext
      [.decl .one "g" (.const 7), .decl .one "g" (.const 8)] with
  | { initializers :=
      [.store (.op .sub [.topAddr, .const 2]) (.const 7),
       .store (.op .sub [.topAddr, .const 3]) (.const 8)],
      functions := [], exceptions := [], context :=
      { globals := [("g", (.one, 3)), ("g", (.one, 2))], globalsSize := 3,
        maxGlobalsSize := 16, bytesInWord := 1, fromNat := _ } } => true
  | _ => false) &&
  (match globalCompileDecs compileContext [.exnDecl "E" .one] with
  | { initializers := [], functions := [], exceptions := [.exnDecl "E" .one],
      context :=
      { globals := [], globalsSize := 1, maxGlobalsSize := 16,
        bytesInWord := 1, fromNat := _ } } => true
  | _ => false) &&
  (match globalCompileDecs compileContext [.name "S" []] with
  | { initializers := [], functions := [], exceptions := [], context :=
      { globals := [], globalsSize := 1, maxGlobalsSize := 16,
        bytesInWord := 1, fromNat := _ } } => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsCompileDecsParity
