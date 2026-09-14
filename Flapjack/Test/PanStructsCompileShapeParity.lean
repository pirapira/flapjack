import Flapjack.PanStructs

namespace Flapjack.Test.PanStructsCompileShapeParity

/-! Direct parity for `pan_structs$compile_shape_def`
    (`pan_structsScript.sml:37`).  The nested cases distinguish the source's
    suffix context from an incorrect lookup through the whole context. -/
def forwardContext : StructContext :=
  [("outer", { fields := [("field", .named "inner")], size := 1 }),
   ("inner", { fields := [("value", .one)], size := 1 })]

def backwardContext : StructContext :=
  [("inner", { fields := [("value", .one)], size := 1 }),
   ("outer", { fields := [("field", .named "inner")], size := 1 })]

def parityGuard : Bool :=
  (match structCompileShape forwardContext .one with
  | .one => true
  | _ => false) &&
  (match structCompileShape forwardContext (.comb [.one, .one]) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structCompileShape forwardContext (.named "outer") with
  | .comb [.comb [.one]] => true
  | _ => false) &&
  (match structCompileShape backwardContext (.named "outer") with
  | .comb [.one] => true
  | _ => false) &&
  (match structCompileShape forwardContext (.named "missing") with
  | .one => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanStructsCompileShapeParity
