import Flapjack.Pancake.PanToCrep

/-!
# Pancake `shape_vars` parity

The expected lists below are transcribed from CakeML's
`cakeml/pancake/pan_to_crepScript.sml:319-322` (`shape_vars_def`).  The
observable is the complete shape/word partition, including Cake's truncation
of a short suffix and its dropping of excess words.
-/

namespace Flapjack.Test.PanShapeVarsParity

open Flapjack

def one : Shape := .one
def pair : Shape := .comb [.one, .one]
def named : Shape := .named "Pair"

example : shapeVars ([] : List Shape) ([1, 2, 3] : List Nat) = [] := by rfl

example :
  shapeVars [one, pair, named] ([10, 11, 12, 13, 14] : List Nat) =
    [(one, [10]), (pair, [11, 12]), (named, [13])] := by
  simp [shapeVars, Shape.shapeSize, one, pair, named]

example :
  shapeVars [pair, one] ([7] : List Nat) =
    [(pair, [7]), (one, [])] := by
  simp [shapeVars, Shape.shapeSize, one, pair]

end Flapjack.Test.PanShapeVarsParity
