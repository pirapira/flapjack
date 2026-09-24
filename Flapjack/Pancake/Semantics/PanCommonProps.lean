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

/-- Exact port of HOL `max_foldr_lt`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:768`): a member of a
    list is strictly below the fold with `max` (starting from `n`) plus any
    positive slack `m`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "max_foldr_lt"]
theorem max_foldr_lt (values : List Nat) (x n m : Nat) (hmem : x ∈ values)
    (hle : n ≤ x) (hm : 0 < m) : x < values.foldr max n + m :=
  mem_lt_foldr_max_add values x n m hmem hle hm

/-- Exact port of HOL `MAP3_MAP2`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:827`): a three-way
    pointwise map is a two-way pointwise map over the first two zipped lists
    when the lengths agree; `UNCURRY f` is `fun p z => f p.1 p.2 z`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "MAP3_MAP2"]
theorem MAP3_MAP2 {α β γ δ : Type} (f : α → β → γ → δ) (l1 : List α)
    (l2 : List β) (l3 : List γ) (h1 : l1.length = l3.length)
    (h2 : l2.length = l3.length) :
    panMap3 f l1 l2 l3 =
      panMap2 (fun (pair : α × β) (z : γ) => f pair.1 pair.2 z)
        (l1.zip l2) l3 :=
  panMap3_eq_map2_zip f l1 l2 l3 h1 h2

/-- Exact port of HOL `all_distinct_take`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:384`):
    `ALL_DISTINCT` is closed under `TAKE`; HOL carries the bound
    `n <= LENGTH ns`, so it is retained here. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_take"]
theorem all_distinct_take {α : Type} (ns : List α) (n : Nat) (h : ns.Nodup)
    (_hbound : n ≤ ns.length) : (ns.take n).Nodup :=
  nodup_take ns n h

/-- Exact port of HOL `all_distinct_drop`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:392`):
    `ALL_DISTINCT` is closed under `DROP`; HOL carries the bound
    `n <= LENGTH ns`, so it is retained here. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "all_distinct_drop"]
theorem all_distinct_drop {α : Type} (ns : List α) (n : Nat) (h : ns.Nodup)
    (_hbound : n ≤ ns.length) : (ns.drop n).Nodup :=
  nodup_drop ns n h

/-- Exact port of HOL `distinct_lists_append`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:108`): an
    `ALL_DISTINCT` concatenation has pairwise-disjoint halves; HOL
    `distinct_lists` is the proposition `ListDisjoint`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_append"]
theorem distinct_lists_append {α : Type} (xs ys : List α)
    (h : (xs ++ ys).Nodup) : ListDisjoint xs ys :=
  listDisjoint_append xs ys h

/-- Exact port of HOL `distinct_lists_cons`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:125`): pairwise
    disjointness of concatenations restricts to the inner halves. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_cons"]
theorem distinct_lists_cons {α : Type} (ns xs ys zs : List α)
    (h : ListDisjoint (ns ++ xs) (ys ++ zs)) : ListDisjoint xs zs :=
  listDisjoint_of_append_left ns xs ys zs h

/-- Exact port of HOL `distinct_lists_simp_cons`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:133`): pairwise
    disjointness survives dropping the head of the right list. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "distinct_lists_simp_cons"]
theorem distinct_lists_simp_cons {α : Type} (xs : List α) (y : α) (ys : List α)
    (h : ListDisjoint xs (y :: ys)) : ListDisjoint xs ys :=
  listDisjoint_of_cons_right xs y ys h

end Flapjack
