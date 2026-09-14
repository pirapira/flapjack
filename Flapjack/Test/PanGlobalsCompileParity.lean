import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileParity

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-! Direct parity for `pan_globals$compile_def`
    (`pan_globalsScript.sml:69`). -/
def parityGuard : Bool :=
  (match globalCompileProg compileContext
      (.assign .local "x" (.const 7)) with
  | .assign .local "x" (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "g" (.const 7)) with
  | .store (.op .sub [.topAddr, .const 8]) (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "missing" (.const 7)) with
  | .skip => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.seq .skip (.return (.const 7))) with
  | .seq .skip (.return (.const 7)) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.return (.var .global "g")) with
  | .return (.load .one (.op .sub [.topAddr, .const 8])) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsCompileParity
