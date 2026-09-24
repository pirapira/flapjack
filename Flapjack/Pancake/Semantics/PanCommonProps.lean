import Flapjack.FiniteMap.Basic
import Flapjack.HolRef
import Flapjack.PanToCrepMaxList
import Flapjack.Pancake.PanLang

/-!
# Pancake `pan_commonProps`

Lean counterpart of `cakeml/pancake/semantics/pan_commonPropsScript.sml`.  The
HOL script contains the context well-formedness predicates shared by the
Pan-to-Crep correctness proof: `ctxt_max` bounds the variable slots and
`no_overlap` requires distinct variables to occupy disjoint slots.  Both are
stated over the extensional finite-map model from `Flapjack.FiniteMap.Basic`.
-/

namespace Flapjack

/-- HOL `ctxt_max_def` (`cakeml/pancake/semantics/pan_commonPropsScript.sml:11`):
    the slot bound is non-negative and every slot assigned by the context map
    is at most `n`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "ctxt_max_def"]
def ctxtMax (n : Nat) (fm : FiniteMap String (Shape × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ v a xs, FLOOKUP fm v = some (a, xs) → ∀ x ∈ xs, x ≤ n

/-- HOL `no_overlap_def` (`cakeml/pancake/semantics/pan_commonPropsScript.sml:18`):
    every variable's slot list is duplicate-free, and variables whose slot sets
    intersect are the same variable. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "no_overlap_def"]
def noOverlap (fm : FiniteMap String (Shape × List Nat)) : Prop :=
  (∀ x a xs, FLOOKUP fm x = some (a, xs) → xs.Nodup) ∧
    ∀ x y a b xs ys, FLOOKUP fm x = some (a, xs) → FLOOKUP fm y = some (b, ys) →
      (∃ z, z ∈ xs ∧ z ∈ ys) → x = y

/-- HOL `opt_mmap_eq_some`: an optional map succeeds exactly when every
    element maps to the corresponding `some` value. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_eq_some"]
theorem optMmapEqSome (xs : List α) (f : α → Option β) (ys : List β) :
    xs.mapM f = some ys ↔ xs.map f = ys.map some := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x xs ih =>
        cases hfx : f x with
        | none => simp [List.mapM_cons, hfx] at h
        | some value =>
            cases htail : xs.mapM f with
            | none => simp [List.mapM_cons, hfx, htail] at h
            | some rest =>
                have hpair : value :: rest = ys := by
                  simpa [List.mapM_cons, hfx, htail] using h
                cases ys with
                | nil => simp at hpair
                | cons y ys =>
                    simp only [List.cons.injEq] at hpair
                    rcases hpair with ⟨rfl, rfl⟩
                    simpa [hfx] using ih rest htail
  · intro h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x xs ih =>
        cases ys with
        | nil => simp at h
        | cons y ys =>
            simp only [List.map_cons, List.cons.injEq] at h
            rcases h with ⟨hfx, htail⟩
            simp [List.mapM_cons, hfx, ih ys htail]

/-- The empty context map satisfies `ctxt_max` for every bound. -/
theorem ctxtMax_empty (n : Nat) :
    ctxtMax n (FEMPTY : FiniteMap String (Shape × List Nat)) := by
  refine ⟨Nat.zero_le n, ?_⟩
  intro v a xs hlookup
  simp at hlookup

/-- The empty context map satisfies `no_overlap`. -/
theorem noOverlap_empty :
    noOverlap (FEMPTY : FiniteMap String (Shape × List Nat)) := by
  refine ⟨?_, ?_⟩
  · intro x a xs hlookup
    simp at hlookup
  · intro x y a b xs ys hx hy hinter
    simp at hx

/-- Rendering of HOL `alist_to_fmap` (`FOLDR (λ(k,v) m. FUPDATE m (k,v)) FEMPTY`).
    The HOL definition lives in HOL's `alistTheory`, outside the CakeML tree, so
    this helper is untagged here. -/
def alistToFmap [BEq α] (entries : List (α × β)) : FiniteMap α β :=
  entries.foldr (fun entry map => FUPDATE map entry) FEMPTY

/-- Exact port of HOL `fm_empty_zip_alist`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:426`): zipping two
    equal-length lists with duplicate-free keys makes the list fold and the
    right fold of `FUPDATE` agree. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "fm_empty_zip_alist"]
theorem fmEmptyZipAlist [BEq α] [LawfulBEq α] (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) (hdistinct : xs.Nodup) :
    FUPDATE_LIST FEMPTY (xs.zip ys) = alistToFmap (xs.zip ys) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [FUPDATE_LIST, alistToFmap]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := Nat.succ.inj hlen
          have hmem : x ∉ xs := (List.nodup_cons.mp hdistinct).1
          have hnodup : xs.Nodup := (List.nodup_cons.mp hdistinct).2
          rw [List.zip_cons_cons, FUPDATE_LIST_cons]
          change FUPDATE_LIST (FUPDATE FEMPTY (x, y)) (xs.zip ys) =
            FUPDATE (alistToFmap (xs.zip ys)) (x, y)
          rw [← ih ys hlen' hnodup]
          have hkeys : (xs.zip ys).map Prod.fst = xs :=
            List.map_fst_zip (Nat.le_of_eq hlen')
          have hnotin : x ∉ (xs.zip ys).map Prod.fst := by
            rw [hkeys]; exact hmem
          exact (FUPDATE_FUPDATE_LIST_commutes FEMPTY x y (xs.zip ys) hnotin).symm

/-- Exact port of HOL `MAX_LIST_add_not_mem`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:642`): `MAX_LIST xs + 1`
    is never a member of `xs`.  `maxList` is the faithful `rich_list$MAX_LIST`
    port (`Flapjack/PanToCrepMaxList.lean`). -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "MAX_LIST_add_not_mem"]
theorem MAX_LIST_add_not_mem (values : List Nat) : maxList values + 1 ∉ values :=
  maxList_add_one_not_mem values

/-- Exact port of HOL `MAX_LIST_i_genlist`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:712`): the maximum of
    `GENLIST I n` is `n - 1`; `List.range n` is `GENLIST I n`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "MAX_LIST_i_genlist"]
theorem MAX_LIST_i_genlist (n : Nat) : maxList (List.range n) = n - 1 :=
  maxList_range n

end Flapjack
