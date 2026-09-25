import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Exact `LIST_REL` carrier for HOL `vshapes_args_rel_imp_eq_len_MAP`

HOL `panSemScript.sml:740-748`:

```
Theorem vshapes_args_rel_imp_eq_len_MAP:
  !vshapes args.
    LIST_REL (\vshape arg. SND vshape = shape_of arg) vshapes args ==>
     LENGTH vshapes = LENGTH args /\ MAP SND vshapes = MAP shape_of args
```

Lean core in this toolchain has no `List.Forall₂`, so the exact HOL `LIST_REL`
predicate is defined here as the FLAPJACK-specific inductive `ListRelHOL`
(same two constructors, same shapes, no extra hypotheses).  The theorem is then
stated over the exact `mlstring`/`shape`/`v` carriers and the tagged
`shapeOfHOLExact`.  Direct original-HOL rows live in
`scripts/hol-probes/pan_sem_e2e_probe.out`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL)

/-- Exact HOL `LIST_REL` carrier: a two-constructor relation over lists with the
    same nil/cons shapes (mismatched lengths are not related). -/
inductive ListRelHOL {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRelHOL R [] []
  | cons {head tail head' tail'} : R head head' → ListRelHOL R tail tail' →
      ListRelHOL R (head :: tail) (head' :: tail')

/-- Exact port of HOL `vshapes_args_rel_imp_eq_len_MAP`
    (`cakeml/pancake/semantics/panSemScript.sml:740`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "vshapes_args_rel_imp_eq_len_MAP"]
theorem vshapes_args_rel_imp_eq_len_MAP {width : Nat} [NeZero width]
    (vshapes : List (MlS × ShapeHOL)) (args : List (ValueHOL width))
    (h : ListRelHOL (fun vshape arg => vshape.2 = shapeOfHOLExact arg) vshapes args) :
    vshapes.length = args.length ∧
      vshapes.map Prod.snd = args.map shapeOfHOLExact := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hr _ ih =>
      obtain ⟨hlen, hmap⟩ := ih
      refine ⟨by simpa using hlen, ?_⟩
      simp only [List.map_cons, hr, hmap]

end Flapjack
