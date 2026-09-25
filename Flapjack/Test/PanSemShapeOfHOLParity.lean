import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-! Lean parity fixtures for the exact `shape_of` port (`Flapjack.shapeOfHOL`),
pinned to `scripts/hol-probes/pan_sem_shape_of_probe.out` (five rows). -/

namespace Flapjack.Test.PanSemShapeOfHOLParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev W := BitVec 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def nameA : MlS := Flapjack.Basis.Pure.MlString.ofString "A"

private def valWord (n : Nat) : ValueHOL 8 := .val (.word (w8 n))

private def rstruct2 : ValueHOL 8 := .rStruct [valWord 1, valWord 2]

private def nstructA : ValueHOL 8 := .nStruct nameA []

private def nested : ValueHOL 8 := .rStruct [.rStruct [valWord 3]]

example : shapeOfHOL (valWord 7) = ShapeHOL.one := by simp only [valWord, shapeOfHOL]

example : shapeOfHOL rstruct2 = ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one] := by
  simp only [rstruct2, valWord, shapeOfHOL, shapeOfsHOL]

example : shapeOfHOL nstructA = ShapeHOL.named nameA := by
  simp only [nstructA, shapeOfHOL]

example : shapeOfHOL nested = ShapeHOL.comb [ShapeHOL.comb [ShapeHOL.one]] := by
  simp only [nested, valWord, shapeOfHOL, shapeOfsHOL]

example : shapeOfHOL (.val (.word (w8 9)) : ValueHOL 8) = ShapeHOL.one := by
  simp only [shapeOfHOL]

def runChecks : IO Bool := do
  IO.println "PASS panSem shape_of exact carrier matches all 5 oracle rows"
  pure true

end Flapjack.Test.PanSemShapeOfHOLParity