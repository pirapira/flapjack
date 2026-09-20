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

/- Direct parity for `pan_structs$get_names_def`
   (`pan_structsScript.sml:235`).  Cake prepends each Name declaration while
   traversing the source list, so the final structure environment is in
   reverse Name order and ignores every non-Name declaration. -/
def getNamesParityGuard : Bool :=
  let context : StructPassContext :=
    { structs := [], locals := [], globals := [] }
  match structGetNames context
      [.decl .one "global" (.const 0),
       .name "First" [("a", .comb [.one, .one])],
       .function
         { name := "f", inline := false, exported := false, params := [],
           body := .skip, returnShape := .one },
       .name "Second" [("b", .one)]] with
  | { structs := [("Second", second), ("First", first)],
      locals := [], globals := [] } =>
      match second.fields, second.size, second.shapedFields,
        first.fields, first.size, first.shapedFields with
      | [("b", .one)], 0, [], [("a", .comb [.one, .one])], 0, [] => true
      | _, _, _, _, _, _ => false
  | _ => false

#eval getNamesParityGuard
#guard getNamesParityGuard

end Flapjack.Test.PanStructsCompileShapeParity
