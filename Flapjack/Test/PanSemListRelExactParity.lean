import Flapjack.Pancake.Semantics.PanSem.ListRelExact

/-!
Parity for the exact HOL `vshapes_args_rel_imp_eq_len_MAP`
(`panSemScript.sml:740`).  The direct original-HOL rows are
`vshapes_args_rel_ok=T`, `vshapes_args_rel_concl=T`,
`vshapes_args_rel_mismatch=F` in `scripts/hol-probes/pan_sem_e2e_probe.out`.
-/

namespace Flapjack.Test.PanSemListRelExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := BitVec 8

abbrev exampleVshapes : List (MlS × ShapeHOL) := [(ml "a", ShapeHOL.one)]

abbrev exampleArgs : List (ValueHOL 8) := [.val (.word (3 : Word8))]

abbrev exampleMismatch : List (ValueHOL 8) := [.rStruct []]

/-- HOL `vshapes_args_rel_ok`: the relation holds for one matching pair. -/
example : ListRelHOL (fun vshape arg => vshape.2 = shapeOfHOLExact arg)
    exampleVshapes exampleArgs :=
  ListRelHOL.cons (by simp [shapeOfHOLExact.eq_def]) ListRelHOL.nil

/-- HOL `vshapes_args_rel_concl`: the length and map conclusions hold. -/
example : exampleVshapes.length = exampleArgs.length ∧
    exampleVshapes.map Prod.snd = exampleArgs.map shapeOfHOLExact :=
  vshapes_args_rel_imp_eq_len_MAP (width := 8) exampleVshapes exampleArgs
    (ListRelHOL.cons (by simp [shapeOfHOLExact.eq_def]) ListRelHOL.nil)

/-- HOL `vshapes_args_rel_mismatch`: a shape mismatch does not relate (the
    HOL oracle row is `vshapes_args_rel_mismatch=F`). -/
example : shapeOfHOLExact (width := 8) (exampleMismatch.head (by simp [exampleMismatch])) ≠
    ShapeHOL.one := by
  simp [exampleMismatch, shapeOfHOLExact.eq_def]

def runChecks : IO Bool := do
  IO.println "PASS exact panSem vshapes_args_rel_imp_eq_len_MAP (3 HOL rows)"
  pure true

end Flapjack.Test.PanSemListRelExactParity
