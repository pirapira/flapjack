import Flapjack.PanStructs

namespace Flapjack.Test.PanStructsOldExpShapeParity

/-! Direct parity for `pan_structs$old_exp_shape_def`
    (`pan_structsScript.sml:70`). -/
def context : StructPassContext :=
  { structs := [("Pair", { fields := [("left", .one),
      ("right", .comb [.one, .one])], size := 3 })]
    locals := [("local", .comb [.one, .one])]
    globals := [("global", .named "Pair")] }

def parityGuard : Bool :=
  (match structOldExpShape context (.var .local "local" : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context (.var .global "global" : Exp Nat) with
  | .named "Pair" => true
  | _ => false) &&
  (match structOldExpShape context
      (.rStruct [.const 1, .const 2] : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context
      (.rField 1 (.rStruct [.const 1, .const 2]) : Exp Nat) with
  | .one => true
  | _ => false) &&
  (match structOldExpShape context (.nStruct "Pair" [] : Exp Nat) with
  | .named "Pair" => true
  | _ => false) &&
  (match structOldExpShape context
      (.nField "right" (.nStruct "Pair" []) : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context
      (.load (.comb [.one, .one]) (.const 0)) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context (.const 0) with
  | .one => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanStructsOldExpShapeParity
