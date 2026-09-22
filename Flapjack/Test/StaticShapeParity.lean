import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_shape_def`
    (`cakeml/pancake/panStaticScript.sml:759-773`). -/

def shapeParityScope : Scope := .funScope "f" ""

def shapeParityContext : StructContext :=
  [("Pair", { fields := [], size := 2 })]

#guard
  staticResultOk
    (checkShape shapeParityContext "line: " shapeParityScope .one)

#guard
  staticResultOk
    (checkShape shapeParityContext "line: " shapeParityScope
      (.comb [.one, .named "Pair", .comb [.one, .one]]))

#guard
  staticResultErrorMessage
    (checkShape shapeParityContext "line: " shapeParityScope (.named "Missing")) ==
      some "line: struct name Missing is not in scope in function f\n"

#guard
  staticResultErrorMessage
    (checkShape shapeParityContext "line: " shapeParityScope
      (.comb [.one, .named "Missing", .named "Pair"])) ==
      some "line: struct name Missing is not in scope in function f\n"

end Flapjack
