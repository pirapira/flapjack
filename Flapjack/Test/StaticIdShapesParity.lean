import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_id_shapes_def`
    (`cakeml/pancake/panStaticScript.sml:776-797`). -/

def idShapesContext : StructContext :=
  [("Pair", { fields := [], size := 2 })]

#guard
  staticResultOk
    (checkIdShapes idShapesContext "line: " (.funScope "f" "")
      [("x", .one), ("pair", .named "Pair")])

#guard
  staticResultErrorMessage
    (checkIdShapes idShapesContext "line: " (.funScope "f" "")
      [("missing", .named "Unknown")]) ==
      some "line: struct name Unknown is not in scope in function f parameter missing\n"

#guard
  staticResultErrorMessage
    (checkIdShapes idShapesContext "line: " (.structScope "Record" "")
      [("field", .named "Unknown")]) ==
      some "line: struct name Unknown is not in scope in declaration of field field in named struct Record\n"

#guard
  staticResultErrorMessage
    (checkIdShapes idShapesContext "line: " .topLevel [("x", .one)]) ==
      some ("line: parameter or field found in unexpected scope in top-level declaration\n" ++
        "this should never happen. please report to a compiler developer\n")

end Flapjack
