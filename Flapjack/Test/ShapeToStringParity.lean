import Flapjack.Language

/-! Parity checks for Pancake `shape_to_str_def`, backed by
    `scripts/hol-probes/shape_to_str_probe.out`. -/

namespace Flapjack.Test.ShapeToStringParity

open Flapjack

def parityGuard : Bool :=
  Shape.shapeToString .one == "1" &&
    Shape.shapeToString (.comb []) == "{}" &&
    Shape.shapeToString (.comb [.one, .named "Pair", .comb [.one, .one]]) ==
      "{1,Pair,{1,1}}" &&
    Shape.shapeToString (.named "Pair") == "Pair"

#guard parityGuard
#eval parityGuard

end Flapjack.Test.ShapeToStringParity
