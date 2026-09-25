import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL

/-!
Parity fixtures for the exact `panSem$mem_load` port `memLoadHOLExact`
(`@[hol ... "mem_load_def"]`) against
`scripts/hol-probes/pan_sem_mem_load_exact_probe.out` (6 rows).
-/

namespace Flapjack.Test.PanSemMemLoadExactParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev W := BitVec 8
private abbrev M := Flapjack.Basis.Pure.MlString.MlString

private def mStr (s : String) : M := Flapjack.Basis.Pure.MlString.ofString s

private def demoContext : StructContextHOLM :=
  [(mStr "A", { fields := [(mStr "f", ShapeHOL.one)], size := 2 })]

private def mem7 : W → HolWordLab 8 := fun _ => .word (BitVec.ofNat 8 7)

private def memInc : W → HolWordLab 8 := fun a => .word (BitVec.ofNat 8 (a.toNat + 1))

private def mem5 : W → HolWordLab 8 := fun _ => .word (BitVec.ofNat 8 5)

private def memTen : W → HolWordLab 8 := fun a => .word (BitVec.ofNat 8 (10 * a.toNat))

macro "ml_unfold" : tactic =>
  `(tactic|
    (simp only [memLoadHOLExact, memLoadsHOLExact, memLoadFldsHOLExact, bytesInWordHOL,
        mem7, mem5, memInc, memTen, demoContext, mStr,
        Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
        Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL]
     first | rfl | decide | simp))

-- ml_one_hit
example : memLoadHOLExact (ShapeHOL.one) (0 : W) (fun a => a == 0) mem7 [] =
    some (.val (.word 7)) := by ml_unfold

-- ml_one_miss
example : memLoadHOLExact (ShapeHOL.one) (0 : W) (fun _ => false) mem7 [] = none := by ml_unfold

-- ml_comb
example : memLoadHOLExact (ShapeHOL.comb [.one, .one]) (0 : W)
    (fun a => a == 0 || a == 1) memInc [] =
    some (.rStruct [.val (.word 1), .val (.word 2)]) := by ml_unfold

-- ml_named_hit
example : memLoadHOLExact (ShapeHOL.named (mStr "A")) (0 : W)
    (fun a => a == 0) mem5 demoContext =
    some (.nStruct (mStr "A") [(mStr "f", .val (.word 5))]) := by ml_unfold

-- ml_named_miss
example : memLoadHOLExact (ShapeHOL.named (mStr "Z")) (0 : W)
    (fun a => a == 0) mem5 demoContext = none := by ml_unfold

-- ml_comb_offset
example : memLoadHOLExact (ShapeHOL.comb [.one, .one]) (0 : W)
    (fun a => a == 0 || a == 1) memTen [] =
    some (.rStruct [.val (.word 0), .val (.word 10)]) := by ml_unfold

def runChecks : IO Bool := do
  IO.println "PASS panSem mem_load exact carrier matches all 6 oracle rows"
  pure true

end Flapjack.Test.PanSemMemLoadExactParity