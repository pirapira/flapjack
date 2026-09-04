import Pancake.Language
import Pancake.Static
import Pancake.PanToCrep
import Pancake.Compile

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

def crepContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], maxVar := 1, bytesInWord := 1 }

example :
    compileExp crepContext (Exp.var .local "pair") =
      ([.var 0, .var 1], .comb [.one, .one]) := by
  simp [compileExp, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.rField 1 (Exp.var .local "pair")) =
      ([.var 1], .one) := by
  simp [compileExp, compileField, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.const (α := Nat) 7) = ([.const 7], .one) := by
  simp [compileExp]

example :
    loadShape (0 : Nat) 4 2 (.var 3) =
      [.load (.var 3), .load (.op .add [.var 3, .const 4])] := by
  simp [loadShape]

example :
    cexpHeads ([ [.var 0], [.var 1] ] : List (List (CrepExp Nat))) =
      some [.var 0, .var 1] := by
  rfl

example : compileProg crepContext .skip = (.skip : CrepProg Nat) := by
  simp [compileProg]

example :
    compileProg crepContext (.return (.const (α := Nat) 7)) =
      .return [.const 7] := by
  simp [compileProg, compileExp]

example :
    compileProg crepContext (.seq .skip (.tick : Prog Nat)) =
      .seq .skip .tick := by
  simp [compileProg]

end Pancake
