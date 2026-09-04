import Pancake.Language
import Pancake.Static

namespace Pancake

def sampleShape : Shape := .comb [.one, .comb [.one, .one]]

example : Shape.shapeSize sampleShape = 3 := by
  simp [sampleShape, Shape.shapeSize]

example : nestedSeq ([] : List (Prog Nat)) = .skip := by
  rfl

example :
    expLocalVars (.op .add [.var .local "x", .var .global "g", .const 1]) = ["x"] := by
  native_decide

example :
    expGlobalVars (Exp.nStruct (α := Nat) "Pair"
      [("left", .var .local "x"), ("right", .var .global "g")]) = ["g"] := by
  native_decide

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

example : isWfShape pairContext (.named "Pair") = true := by
  native_decide

example : isWfShape pairContext (.comb [.one, .named "Pair"]) = true := by
  native_decide

example : isWfShape pairContext (.named "Missing") = false := by
  native_decide

example : isWfContext pairContext = true := by
  native_decide

example : shapeSizeWithContext pairContext (.named "Pair") = 2 := by
  native_decide

def duplicateContext : StructContext :=
  [("Pair", { fields := [], size := 0 }), ("Pair", { fields := [], size := 0 })]

example : isWfContext duplicateContext = false := by
  native_decide

example : validateDecl pairContext (.decl .one "answer" (.const 42)) = true := by
  native_decide

example : validateDecl pairContext (.decl (.named "Missing") "bad" (.const 0)) = false := by
  native_decide

end Pancake
