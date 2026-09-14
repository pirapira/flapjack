import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileExpParity

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-! Direct parity for `pan_globals$compile_exp_def`
    (`pan_globalsScript.sml:18`). -/
def parityGuard : Bool :=
  (match globalCompileExp compileContext (.var .local "x") with
  | .var .local "x" => true
  | _ => false) &&
  (match globalCompileExp compileContext (.var .global "g") with
  | .load .one (.op .sub [.topAddr, .const 8]) => true
  | _ => false) &&
  (match globalCompileExp compileContext (.var .global "missing") with
  | .const 0 => true
  | _ => false) &&
  (match globalCompileExp compileContext .topAddr with
  | .op .sub [.topAddr, .const 16] => true
  | _ => false) &&
  (match globalCompileExp compileContext
      (.op .add [.var .global "g", .topAddr]) with
  | .op .add
      [.load .one (.op .sub [.topAddr, .const 8]),
       .op .sub [.topAddr, .const 16]] => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsCompileExpParity
