import Flapjack.HolRef
import Flapjack.PanToCrepMaxList
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.CrepInline.Pass

/-! Exact theorem counterpart for CakeML's `crep_inlineProofScript.sml`.

    The declarations here are stated over Lean's `(List.range n).map f`, the
    image of HOL's `GENLIST f n`, and over `Nat`, matching the source's
    `:num` variables. Each carries the HOL declaration name and argument
    order verbatim. -/

namespace Flapjack

/-- CakeML's `genlist_less_than` (`crep_inlineProofScript.sml:629`): every value
    in `GENLIST (λx. a + SUC x) n` is strictly above `a`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_less_than"]
theorem genlist_less_than (n a v : Nat) :
    v ∈ (List.range n).map (fun x => a + (x + 1)) → a < v := by
  intro hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  omega

/-- CakeML's `genlist_not_in` (`crep_inlineProofScript.sml:636`): values at or
    below `a` do not occur in `GENLIST (λx. a + SUC x) n`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_not_in"]
theorem genlist_not_in (n a v : Nat) (h : v ≤ a) :
    v ∉ (List.range n).map (fun x => a + (x + 1)) := by
  intro hmem
  have := genlist_less_than n a v hmem
  omega

/-- CakeML's `genlist_all_distinct` (`crep_inlineProofScript.sml:643`):
    `GENLIST (λx. a + SUC x) n` has no duplicates. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_all_distinct"]
theorem genlist_all_distinct (n a : Nat) :
    ((List.range n).map (fun x => a + (x + 1))).Nodup :=
  List.Pairwise.map (fun x => a + (x + 1))
    (fun _left _right hne heq =>
      hne (Nat.add_right_cancel (Nat.add_left_cancel heq)))
    List.nodup_range

/-- CakeML's `MORE_THEN_NOT_MAX_LIST` (`crep_inlineProofScript.sml:1562`): a
    value strictly above `MAX_LIST l` does not occur in `l`.  Lean's `maxList`
    is the faithful port of HOL's `rich_list$MAX_LIST`
    (`Flapjack/PanToCrepMaxList.lean`), so this is the same fact as HOL's
    `MAX_LIST_NOT_MEM`, stated here under the `crep_inline` declaration name. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MORE_THEN_NOT_MAX_LIST"]
theorem moreThenNotMaxList (l : List Nat) (x : Nat) (h : maxList l < x) :
    x ∉ l :=
  maxList_not_mem x l (by omega)

/-- CakeML's `max_list_genlist_add_suc_val`
    (`crep_inlineProofScript.sml:2579`): the maximum of
    `GENLIST (λx. SUC x + k) n` is `n + k` for `n ≠ 0`.  `(List.range n).map f`
    is Lean's image of HOL's `GENLIST f n`, and `maxList` is the faithful
    `rich_list$MAX_LIST` port (`Flapjack/PanToCrepMaxList.lean`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "max_list_genlist_add_suc_val"]
theorem max_list_genlist_add_suc_val (k : Nat) :
    ∀ n, n ≠ 0 →
      maxList ((List.range n).map (fun x => (x + 1) + k)) = n + k :=
  maxList_genlist_add_suc_val k

/-- CakeML's `cont_res` (`crep_inlineProofScript.sml:2168`): a finite,
    "continuous" result predicate.  `NONE` and `SOME` results that stop the
    walk (`Break`, `Continue`, `Error`) are `T`; all other results
    (`TimeOut`, `Return`, `Exception`, `FinalFFI`) are `F`.  The carrier is
    `CrepResultHOL`, the exact constructor-by-constructor encoding of
    `crepSem$result` (`crepSemScript.sml:37-44`), so the fourth HOL equation
    `cont_res _ = F` is the four remaining constructors. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "cont_res_def"]
def contResHOL : Option (CrepResultHOL α ε) → Bool
  | none => true
  | some (.break _) => true
  | some (.continue _) => true
  | some .error => true
  | some _ => false

/-- CakeML's `MEM_MAP2_IMP` (`crep_inlineProofScript.sml:2233`): every element
    of a pointwise map comes from elements of both input lists.  We keep the
    Flapjack lemma name `panMap2_mem`; `panMap2` is the exact `MAP2` port. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MEM_MAP2_IMP"]
theorem panMap2_mem {α β γ : Type} {f : α → β → γ} {l1 : List α} {l2 : List β}
    {x : γ} (hmem : x ∈ panMap2 f l1 l2) :
    ∃ y1 y2, x = f y1 y2 ∧ y1 ∈ l1 ∧ y2 ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => simp [panMap2] at hmem
  | cons a as ih =>
      cases l2 with
      | nil => simp [panMap2] at hmem
      | cons b bs =>
          simp only [panMap2, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact ⟨a, b, heq, by simp, by simp⟩
          · obtain ⟨y1, y2, heq, h1, h2⟩ := ih hmem
            exact ⟨y1, y2, heq, by simp [h1], by simp [h2]⟩

/-- CakeML's `not_some_is_none` (`crep_inlineProofScript.sml:778`): an option
    with no `SOME` inhabitant is `NONE`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_some_is_none"]
theorem not_some_is_none {α : Type u} (a : Option α) :
    (∀ v, a ≠ some v) ↔ a = none := by
  cases a <;> simp

/-- CakeML's `fdom_eq_flookup_thm` (`crep_inlineProofScript.sml:784`): two
    finite maps have the same domain iff each lookup in one is supported in the
    other and a missing lookup in the first is missing in the second.  `FDOM`
    is the repo finite-map domain predicate (`Flapjack/FiniteMap/Basic.lean`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_eq_flookup_thm"]
theorem fdom_eq_flookup_thm {α : Type} {β : Type} (f1 f2 : FiniteMap α β) :
    FDOM f1 = FDOM f2 ↔
      (∀ x, (∃ v, FLOOKUP f1 x = some v) → (∃ v, FLOOKUP f2 x = some v)) ∧
      (∀ x, FLOOKUP f1 x = none → FLOOKUP f2 x = none) := by
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨v, hv⟩ := hx
      have hv' : f1 x = some v := hv
      have h1 : f1 x ≠ none := by rw [hv']; exact Option.some_ne_none v
      have h2 : f2 x ≠ none := (congrFun h x).mp h1
      cases hf2 : f2 x with
      | none => exact absurd hf2 h2
      | some w => exact ⟨w, hf2⟩
    · intro x hx
      have hx' : f1 x = none := hx
      have h1 : ¬ (f1 x ≠ none) := fun hc => hc hx'
      have h2 : ¬ (f2 x ≠ none) := fun hc => h1 ((congrFun h x).mpr hc)
      cases hf2 : f2 x with
      | none => exact hf2
      | some w => exact (h2 (by rw [hf2]; exact Option.some_ne_none w)).elim
  · rintro ⟨h12, hnone⟩
    funext x
    apply propext
    constructor
    · intro h1
      have hx : ∃ v, f1 x = some v := by
        cases hf1 : f1 x with
        | none => exact absurd hf1 h1
        | some v => exact ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := h12 x hx
      change f2 x ≠ none
      rw [show f2 x = some w from hw]
      exact Option.some_ne_none w
    · intro h2 hf1
      exact h2 (hnone x hf1)

/-- CakeML's `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`):
    `FDOM f` is contained in `FDOM g` iff every defined lookup in `f` is
    defined in `g`.  Subset of the `FDOM` predicate is pointwise implication. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_subset_flookup_thm"]
theorem fdom_subset_flookup_thm {α : Type} {β : Type} (f g : FiniteMap α β) :
    (∀ x, FDOM f x → FDOM g x) ↔
      (∀ x p, FLOOKUP f x = some p → ∃ q, FLOOKUP g x = some q) := by
  constructor
  · intro h x p hp
    have hf : f x ≠ none := by rw [show f x = some p from hp]; exact Option.some_ne_none p
    have hg : g x ≠ none := h x hf
    cases hx : g x with
    | none => exact absurd hx hg
    | some q => exact ⟨q, hx⟩
  · intro h x hf
    cases hx : f x with
    | none => exact absurd hx hf
    | some p =>
        obtain ⟨q, hq⟩ := h x p hx
        change g x ≠ none
        rw [show g x = some q from hq]
        exact Option.some_ne_none q

/-- CakeML's `res_var_commutes_strong` (`crep_inlineProofScript.sml:699`):
    `res_var` updates at two keys commute, with no `n ≠ h` side condition (the
    equal case is definitional).  Stated over the reviewed `resVar`
    (`res_var_def`), whose Boolean key equality reflects HOL's `=` under
    `[LawfulBEq α]`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem res_var_commutes_strong [BEq α] [LawfulBEq α] (lc lc' : FiniteMap α β)
    (n h : α) :
    resVar (resVar lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
    resVar (resVar lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  by_cases hne : n = h
  · subst hne
    rfl
  · exact resVar_commutes lc lc' n h hne

/-- CakeML's `res_var_foldl_commutes_strong`
    (`crep_inlineProofScript.sml:706`): commuting a single `res_var` update past
    a `foldl` of `res_var` over the `ZIP`ped lookup list.  `ZIP (vs, MAP f vs)`
    is Lean's `vs.zip (vs.map f)`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem res_var_foldl_commutes_strong [BEq α] [LawfulBEq α]
    (h : α) (vs : List α) (lc1 lc2 : FiniteMap α β) :
    resVar ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVar lc1)
        (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVar
        (resVar lc1 (h, FLOOKUP lc2 h)) := by
  induction vs generalizing lc1 with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih (resVar lc1 (v, FLOOKUP lc2 v)),
        (res_var_commutes_strong lc1 lc2 v h).symm]

/-- CakeML's `flookup_res_var_is_mem_zip_eq` (`crep_inlineProofScript.sml:802`):
    folding `res_var` over the `ZIP`ped lookup list and then looking up a member
    `x` of the key list reproduces `lc2`'s binding for `x`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem flookup_res_var_is_mem_zip_eq [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (lc1 lc2 : FiniteMap α β) (hx : x ∈ xs) :
    FLOOKUP ((xs.zip (xs.map (FLOOKUP lc2))).foldl resVar lc1) x =
      FLOOKUP lc2 x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [← res_var_foldl_commutes_strong a as lc1 lc2, FLOOKUP_resVar]
      rcases List.mem_cons.mp hx with hxa | hxas
      · subst hxa
        simp
      · by_cases hxa : x = a
        · subst hxa
          simp
        · rw [if_neg (by rw [beq_eq_false_iff_ne.mpr hxa]; simp)]
          exact ih hxas

/-- CakeML's `OPT_MMAP_SOME_ALL` (`crep_inlineProofScript.sml:36`): the optional
    map over a list succeeds for some result exactly when every element maps to
    a `some`.  `List.mapM` is the repo's `OPT_MMAP` carrier (cf. the tagged
    `optMmapEqSome`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_SOME_ALL"]
theorem OPT_MMAP_SOME_ALL {α : Type} {β : Type} (f : α → Option β) (l : List α) :
    (∃ x, l.mapM f = some x) ↔ (∀ e, e ∈ l → ∃ y, f e = some y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
      constructor
      · rintro ⟨x, hx⟩ e he
        rcases List.mem_cons.mp he with hea | he
        · rw [hea]
          cases hfa : f a with
          | none => rw [List.mapM_cons] at hx; simp [hfa] at hx
          | some y => exact ⟨y, rfl⟩
        · cases hfa : f a with
          | none => rw [List.mapM_cons] at hx; simp [hfa] at hx
          | some y =>
              cases hta : as.mapM f with
              | none => rw [List.mapM_cons] at hx; simp [hfa, hta] at hx
              | some rest => exact ih.mp ⟨rest, hta⟩ e he
      · intro h
        obtain ⟨y, hy⟩ := h a List.mem_cons_self
        obtain ⟨ys, hys⟩ := ih.mpr (fun e he => h e (List.mem_cons_of_mem a he))
        exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- CakeML's `OPT_MMAP_ALL_EQ` (`crep_inlineProofScript.sml:47`): two optional
    maps over a list agree when their functions agree on every element. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_ALL_EQ"]
theorem OPT_MMAP_ALL_EQ {α : Type} {β : Type} (f g : α → Option β) (l : List α)
    (h : ∀ e, e ∈ l → f e = g e) : l.mapM f = l.mapM g := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.mapM_cons, h a List.mem_cons_self,
        ih (fun e he => h e (List.mem_cons_of_mem a he))]

/-- CakeML's `fdoms_eq_opt_mmap_flookup_some`
    (`crep_inlineProofScript.sml:1833`): if two finite maps have the same
    domain, an `OPT_MMAP` of `FLOOKUP` over the first succeeding implies the
    same sequence over the second succeeds. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdoms_eq_opt_mmap_flookup_some"]
theorem fdoms_eq_opt_mmap_flookup_some {α : Type} {β : Type} (vs : List α)
    (fm fm' : FiniteMap α β) (vals : List β) (hdom : FDOM fm = FDOM fm')
    (h : vs.mapM (FLOOKUP fm) = some vals) :
    ∃ z, vs.mapM (FLOOKUP fm') = some z := by
  have hall : ∀ e, e ∈ vs → ∃ y, FLOOKUP fm e = some y :=
    (OPT_MMAP_SOME_ALL (FLOOKUP fm) vs).mp ⟨vals, h⟩
  refine (OPT_MMAP_SOME_ALL (FLOOKUP fm') vs).mpr ?_
  intro e he
  obtain ⟨y, hy⟩ := hall e he
  have hmem : FDOM fm' e := by
    rw [← hdom]
    change fm e ≠ none
    change fm e = some y at hy
    rw [hy]
    exact Option.some_ne_none y
  change fm' e ≠ none at hmem
  cases h' : fm' e with
  | none => rw [h'] at hmem; exact absurd rfl hmem
  | some z => exact ⟨z, by change fm' e = some z; rw [h']⟩

/-! ## State and locals relations of `inline_prog_correct` -/

/-- CakeML's `state_rel` (`crep_inlineProofScript.sml:12`): two Crep states agree
    on globals, code, memory, both address domains, clock, endianness, FFI
    state, and base/top addresses.  `CrepHolState` is the exact 11-field
    encoding of `crepSem$state`, so this is a field-by-field port; like HOL it
    leaves `locals` to `locals_rel`/`locals_strong_rel`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineStateRelW below.
def crepInlineStateRel (s t : CrepHolState α σ) : Prop :=
  s.globals = t.globals ∧
  s.code = t.code ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.bigEndian = t.bigEndian ∧
  s.ffi = t.ffi ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress

/-- Finite-map `SUBMAP` for Lean's extensional lookup-function representation:
    every binding of `s` is also a binding of `t` with the same value.  HOL's
    `SUBMAP` holds when `FLOOKUP s` and `FLOOKUP t` agree on `FDOM s`, which is
    exactly this statement.  Untagged infrastructure: HOL's `SUBMAP` is a
    finite-map operation, not a declaration of `crep_inlineProofScript.sml`. -/
def crepHolSubmap {κ : Type} (s t : κ → Option β) : Prop :=
  ∀ n v, s n = some v → t n = some v

/-- Finite-map `SUBMAP_IMP_FUPDATE_SUBMAP`
    (`crep_inlineProofScript.sml:117`): pointwise updates at the same key
    preserve `SUBMAP`.  Stated over `crepHolSubmap`; `|+` is `FUPDATE`, whose
    Boolean key equality reflects HOL's `=` under `[LawfulBEq κ]`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_FUPDATE_SUBMAP {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE f (x, y)) (FUPDATE g (x, y)) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp only [FUPDATE, beq_self_eq_true] at hn ⊢
    exact hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FUPDATE, hb] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_SUBMAP`
    (`crep_inlineProofScript.sml:127`): removing the same key from both sides
    preserves `SUBMAP`.  `\\` is `FDOMSUB`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_DOMSUB_SUBMAP {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FDOMSUB g x) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp [FDOMSUB] at hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FDOMSUB, hb] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_FUPDATE`
    (`crep_inlineProofScript.sml:135`): removing a key from the left and
    inserting it on the right preserves `SUBMAP`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_DOMSUB_FUPDATE {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FUPDATE g (x, y)) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp [FDOMSUB] at hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FDOMSUB, FUPDATE, hb] at hn ⊢
    exact h n v hn

/-- CakeML's `FOLDL_res_var_ZIP_lookup_var` (`crep_inlineProofScript.sml:2661`):
    a fold of `res_var` over the zipped names and their `l'`-lookups is a
    `SUBMAP` (`crepHolSubmap`) of `l1`, so any lookup that `l` already defined at
    a key not in `ns` survives in `l1`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem FOLDL_res_var_ZIP_lookup_var [BEq α] [LawfulBEq α] (l l' l1 : FiniteMap α β)
    (ns : List α) (x : α) (v : β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) l1)
    (hv : FLOOKUP l x = some v) (hx : x ∉ ns) :
    FLOOKUP l1 x = some v := by
  apply hsub x v
  change FLOOKUP ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) x = some v
  rw [FLOOKUP_foldl_resVar_zip_not_mem ns (ns.map (FLOOKUP l')) l x
    (by simp [List.length_map]) hx]
  exact hv

/-- CakeML's `FOLDL_res_var_ZIP_lookup` (`crep_inlineProofScript.sml:2675`):
    the `OPT_MMAP` (`List.mapM`) form of `FOLDL_res_var_ZIP_lookup_var`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem FOLDL_res_var_ZIP_lookup [BEq α] [LawfulBEq α] (l l' l1 : FiniteMap α β)
    (ns xs : List α) (vs : List β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) l1)
    (h : xs.mapM (FLOOKUP l) = some vs)
    (hx : ∀ x, x ∈ xs → x ∉ ns) :
    xs.mapM (FLOOKUP l1) = some vs := by
  have hpt : ∀ x, x ∈ xs → FLOOKUP l1 x = FLOOKUP l x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (FLOOKUP l) xs).mp ⟨vs, h⟩ x hxmem
    have hfl : FLOOKUP l1 x = some y :=
      FOLDL_res_var_ZIP_lookup_var l l' l1 ns x y hsub hy (hx x hxmem)
    rw [hfl, hy]
  rw [OPT_MMAP_ALL_EQ (FLOOKUP l1) (FLOOKUP l) xs hpt]
  exact h

/-! ## HOL-equality (`=`) forms of the `res_var` cluster

FLAPJACK-SPECIFIC (not exact HOL ports).  The HOL declarations below quantify
the key type freely and use propositional equality; `DecidableEq` is Lean's
encoding of HOL `=`, so the `FUPDATE_HOL`/`FDOMSUB_HOL`/`resVarHOL` forms below
remove the `BEq`/`LawfulBEq` side conditions of the production forms.  They are
still NOT exact HOL ports, because they quantify Lean's raw function carrier
`FiniteMap α β := α → Option β` (`Flapjack/FiniteMap/Basic.lean:19`), which
admits infinite-support inhabitants, whereas HOL `α |-> β` is finite-support.
`DecidableEq` alone does not repair that: the statements still range over
functions HOL cannot represent.  A faithful port must quantify
`HolFiniteMapExact α β` (`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean`),
which now provides `update`/`updateList`/`erase`/`resVar` and their lookup
lemmas; that port is tracked by bead `flapjack-pxn.18.3.7.1.3.1.1.3.1`.  The
`_hol` declarations are kept as untagged infrastructure only. -/

theorem submap_imp_fupdate_submap_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE_HOL f (x, y)) (FUPDATE_HOL g (x, y)) := by
  intro n v hn
  simp only [FUPDATE_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn ⊢
    exact hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem submap_imp_domsub_submap_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FDOMSUB_HOL g x) := by
  intro n v hn
  simp only [FDOMSUB_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem submap_imp_domsub_fupdate_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FUPDATE_HOL g (x, y)) := by
  intro n v hn
  simp only [FDOMSUB_HOL, FUPDATE_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem res_var_commutes_strong_hol {α : Type} {β : Type} [DecidableEq α]
    (lc lc' : FiniteMap α β) (n h : α) :
    resVarHOL (resVarHOL lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
      resVarHOL (resVarHOL lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  by_cases hne : n = h
  · subst hne
    rfl
  · exact resVarHOL_commutes lc lc' n h hne

theorem res_var_foldl_commutes_strong_hol {α : Type} {β : Type} [DecidableEq α]
    (h : α) (vs : List α) (lc1 lc2 : FiniteMap α β) :
    resVarHOL ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL lc1)
        (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL
        (resVarHOL lc1 (h, FLOOKUP lc2 h)) := by
  induction vs generalizing lc1 with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih (resVarHOL lc1 (v, FLOOKUP lc2 v)),
        (res_var_commutes_strong_hol lc1 lc2 v h).symm]

theorem flookup_res_var_is_mem_zip_eq_hol {α : Type} {β : Type} [DecidableEq α]
    (xs : List α) (x : α) (lc1 lc2 : FiniteMap α β) (hx : x ∈ xs) :
    FLOOKUP ((xs.zip (xs.map (FLOOKUP lc2))).foldl resVarHOL lc1) x =
      FLOOKUP lc2 x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [← res_var_foldl_commutes_strong_hol a as lc1 lc2, FLOOKUP_resVarHOL]
      rcases List.mem_cons.mp hx with hxa | hxas
      · subst hxa
        simp
      · by_cases hxea : x = a
        · subst hxea
          simp
        · rw [if_neg hxea]
          exact ih hxas

theorem foldl_res_var_zip_lookup_var_hol {α : Type} {β : Type} [DecidableEq α]
    (l l' l1 : FiniteMap α β) (ns : List α) (x : α) (v : β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) l1)
    (hv : FLOOKUP l x = some v) (hx : x ∉ ns) :
    FLOOKUP l1 x = some v := by
  apply hsub x v
  change FLOOKUP ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) x = some v
  rw [FLOOKUP_foldl_resVarHOL_zip_not_mem ns (ns.map (FLOOKUP l')) l x
    (by simp [List.length_map]) hx]
  exact hv

theorem foldl_res_var_zip_lookup_hol {α : Type} {β : Type} [DecidableEq α]
    (l l' l1 : FiniteMap α β) (ns xs : List α) (vs : List β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) l1)
    (h : xs.mapM (FLOOKUP l) = some vs)
    (hx : ∀ x, x ∈ xs → x ∉ ns) :
    xs.mapM (FLOOKUP l1) = some vs := by
  have hpt : ∀ x, x ∈ xs → FLOOKUP l1 x = FLOOKUP l x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (FLOOKUP l) xs).mp ⟨vs, h⟩ x hxmem
    have hfl : FLOOKUP l1 x = some y :=
      foldl_res_var_zip_lookup_var_hol l l' l1 ns x y hsub hy (hx x hxmem)
    rw [hfl, hy]
  rw [OPT_MMAP_ALL_EQ (FLOOKUP l1) (FLOOKUP l) xs hpt]
  exact h

/-- CakeML's `locals_rel` (`crep_inlineProofScript.sml:26`):
    `s.locals SUBMAP t.locals`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsRelW below.
def crepInlineLocalsRel (s t : CrepHolState α σ) : Prop :=
  crepHolSubmap s.locals t.locals

/-- CakeML's `locals_strong_rel` (`crep_inlineProofScript.sml:31`):
    `s.locals = t.locals`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsStrongRelW below.
def crepInlineLocalsStrongRel (s t : CrepHolState α σ) : Prop :=
  s.locals = t.locals

/-- CakeML's `locals_rel_dec_clock` (`crep_inlineProofScript.sml:167`): both
    relations are preserved by `dec_clock`, since only `clock` changes. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsRel_decClockW below.
theorem crepInlineLocalsRel_decClock (s t : CrepHolState α σ)
    (hlocals : crepInlineLocalsRel s t) (hstate : crepInlineStateRel s t) :
    crepInlineLocalsRel (decCrepHolClock s) (decCrepHolClock t) ∧
    crepInlineStateRel (decCrepHolClock s) (decCrepHolClock t) := by
  obtain ⟨hg, hc, hm, hma, hsm, hcl, hbe, hf, hba, hta⟩ := hstate
  refine ⟨?_, ?_⟩
  · simpa only [crepInlineLocalsRel, decCrepHolClock] using hlocals
  · simp only [crepInlineStateRel, decCrepHolClock]
    exact ⟨hg, hc, hm, hma, hsm, by rw [hcl], hbe, hf, hba, hta⟩

/-- Finite-map `FDOM` for Lean's extensional lookup-function representation:
    the predicate holding exactly at the bound keys.  HOL's `FDOM` is a
    finite set; membership `n ∈ FDOM f` is `FLOOKUP f n ≠ NONE`, which is this
    Boolean test.  The key type is arbitrary so the same definition covers both
    `locals` (`Nat` keys) and `code` (`mlstring` keys).  Untagged
    infrastructure: HOL's `FDOM` is a finite-map operation, not a declaration of
    `crep_inlineProofScript.sml`. -/
def crepHolFdom {κ : Type} (f : κ → Option β) : κ → Bool :=
  fun n => (f n).isSome

/-- Finite-map `FDIFF` for Lean's extensional lookup-function representation:
    drop every key selected by `s`.  HOL's `FDIFF f s` restricts `f` to the
    complement of `s`; state membership as a Boolean predicate so the
    operation is executable.  Untagged infrastructure. -/
def crepHolFdiff (f : Nat → Option β) (s : Nat → Bool) : Nat → Option β :=
  fun n => if s n then none else f n

/-- CakeML's `locals_ext_rel` (`crep_inlineProofScript.sml:162`): the locals
    added when running from `a` to `a'` equal those added from `b` to `b'`,
    i.e. `FDIFF a'.locals (FDOM a.locals) = FDIFF b'.locals (FDOM b.locals)`.
    `crepHolFdiff`/`crepHolFdom` render HOL's `FDIFF`/`FDOM` extensionally. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsExtRelW below.
def crepInlineLocalsExtRel (a b a' b' : CrepHolState α σ) : Prop :=
  crepHolFdiff a'.locals (crepHolFdom a.locals) =
    crepHolFdiff b'.locals (crepHolFdom b.locals)

/-- CakeML's `state_rel_code` (`crep_inlineProofScript.sml:1442`): `state_rel`
    without the `code` conjunct, used by the inlining simulation because
    inlining changes `code` but preserves the rest of the state. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineStateRelCodeW below.
def crepInlineStateRelCode (s t : CrepHolState α σ) : Prop :=
  s.globals = t.globals ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.bigEndian = t.bigEndian ∧
  s.ffi = t.ffi ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress

/-- Dropping the whole `FDOM` leaves the empty map. -/
theorem crepHolFdiff_fdom_self (f : Nat → Option β) :
    crepHolFdiff f (crepHolFdom f) = fun _ => none := by
  funext n
  cases h : f n <;> simp [crepHolFdiff, crepHolFdom, h]

/-- `locals_ext_rel` holds when both runs add nothing to their locals. -/
theorem crepInlineLocalsExtRel_self (a b : CrepHolState α σ) :
    crepInlineLocalsExtRel a b a b := by
  simp only [crepInlineLocalsExtRel]
  rw [crepHolFdiff_fdom_self a.locals, crepHolFdiff_fdom_self b.locals]

/-- Finite-map form of Cake `crep_inline$code_inl_rel`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1504-1511`):

    `code_inl_rel inl_fs s t ⇔
       ∀fname args prog. FLOOKUP s.code fname = SOME (args, prog) ⇒
         ∃inl_bag. inl_bag SUBMAP inl_fs ∧
                  FLOOKUP t.code fname = SOME (args, inline_prog inl_bag prog)`

    `CrepInlineFmap.lookup`/`remove`/`submap` mirror HOL
    `FLOOKUP`/`DOMSUB`/`SUBMAP` and `crepInlineProgFmap` is the exact
    `inline_prog` port (see `Flapjack/Pancake/CrepInline/Pass.lean`).  The map
    carrier is a duplicate-free finite map (an entry list carrying a
    duplicate-free key invariant, so `card` equals the domain cardinality)
    rather than HOL's sptree, so no `@[hol]` tag is attached; the statement
    otherwise follows the source clause for clause. -/
def crepInlineCodeInlRel [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ) : Prop :=
  ∀ fname args prog, s.code fname = some (args, prog) →
    ∃ inl_bag : CrepInlineFmap α,
      CrepInlineFmap.submap inl_bag inl_fs ∧
      t.code fname = some (args, crepInlineProgFmap inl_bag prog)

/-- Introduction rule with the witness `inl_bag := inl_fs`. -/
theorem crepInlineCodeInlRel_of_code [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ)
    (h : ∀ fname args prog, s.code fname = some (args, prog) →
      t.code fname = some (args, crepInlineProgFmap inl_fs prog)) :
    crepInlineCodeInlRel inl_fs s t := by
  intro fname args prog hcode
  exact ⟨inl_fs, CrepInlineFmap.submap_refl inl_fs, h fname args prog hcode⟩

/-- A source binding with no target binding refutes the relation. -/
theorem not_crepInlineCodeInlRel_of_target_none
    [BEq FunName] [LawfulBEq FunName] [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ)
    (fname : FunName) (args : List Nat) (prog : CrepProg α)
    (hcode : s.code fname = some (args, prog)) (hnone : t.code fname = none) :
    ¬ crepInlineCodeInlRel inl_fs s t := by
  intro h
  obtain ⟨_bag, _hsub, htarget⟩ := h fname args prog hcode
  rw [hnone] at htarget
  simp at htarget

/-! ## Expression-evaluation invariance under the inline state relations

    These are the Lean counterparts of Cake's
    `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`),
    `eval_state_locals_same_code_fdom_same` (:1467) and `eval_code_inl` (:1513).

    Exactness caveat: the source evaluator `crepSem$eval` is polymorphic in the
    word type, while the Lean evaluator `evalCrepHolExp`
    (`Flapjack/Pancake/Semantics/CrepSem/Eval.lean`) is only defined for the
    concrete `RiscV.Word width` carrier (`[NeZero width]`) and is itself
    untagged; `crepHolFdom` renders `FDOM` as an extensional Boolean predicate
    rather than a HOL finite set; and `crepInlineCodeInlRel`'s bearer is the
    unique-key entry-list finite map.  So no `@[hol]` tag is attached even
    though the statements otherwise follow the source clause for clause. -/

/-- CakeML's `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`):
    `FDOM f ⊆ FDOM g` is exactly "every binding of `f` has a binding of `g` at
    the same key".  Stated for an arbitrary key type since both `locals` and
    `code` are finite maps. -/
theorem crepHolFdom_subset_flookup {κ : Type} (f g : κ → Option β) :
    (∀ n, crepHolFdom f n = true → crepHolFdom g n = true) ↔
      (∀ n p, f n = some p → ∃ q, g n = some q) := by
  constructor
  · intro h n p hp
    exact Option.isSome_iff_exists.mp (h n (by simp [crepHolFdom, hp]))
  · intro h n hn
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨q, hq⟩ := h n p hp
    simp [crepHolFdom, hq]

/-- CakeML's `eval_code_inl` FDOM extraction: `code_inl_rel inl_fs s t` puts
    every key bound in `s.code` into `t.code`, so `FDOM s.code ⊆ FDOM t.code`.
    This is the hypothesis consumed by the expression-evaluation invariance
    below. -/
theorem crepInlineCodeInlRel_fdom_subset
    [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (inlFs : CrepInlineFmap (RiscV.Word width))
    (s t : CrepHolState (RiscV.Word width) σ)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    ∀ n, crepHolFdom s.code n = true → crepHolFdom t.code n = true := by
  intro n hn
  obtain ⟨⟨args, prog⟩, hlookup⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨_inlBag, _hsub, htcode⟩ := hcode n args prog hlookup
  simp [crepHolFdom, htcode]

/-- CakeML's `eval_state_locals_same_code_fdom_same`
    (`crep_inlineProofScript.sml:1467`): expression evaluation depends only on
    the locals and the `state_rel_code` fields, never on `code`, so any two
    states related by `state_rel_code` with equal locals evaluate every
    expression identically.  The `FDOM` subset hypothesis is carried to match
    the HOL statement but is not needed, since `eval` never reads `code`. -/
theorem evalCrepHolExp_state_rel_code [NeZero width]
    (s t : CrepHolState (RiscV.Word width) σ) (e : CrepExp (RiscV.Word width))
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (_hcode : ∀ n, crepHolFdom s.code n = true → crepHolFdom t.code n = true) :
    evalCrepHolExp s e = evalCrepHolExp t e := by
  obtain ⟨hg, hm, hma, _hsm, _hcl, hbe, _hf, hba, hta⟩ := hstate
  have hloc : s.locals = t.locals := hlocals
  induction e using evalCrepHolExp.induct with
  | case1 value => simp only [evalCrepHolExp]
  | case2 name => simp only [evalCrepHolExp, hloc]
  | case3 address ih => simp only [evalCrepHolExp, ih, hm, hma]
  | case4 address ih => simp only [evalCrepHolExp, ih, hm, hma, hbe, crepHolEvalMemLoad32]
  | case5 address ih => simp only [evalCrepHolExp, ih, hm, hma, hbe, crepHolEvalMemLoadByte]
  | case6 address => simp only [evalCrepHolExp, hg]
  | case7 operator expressions ih =>
      simp only [evalCrepHolExp]
      have hmap : List.mapM (evalCrepHolExp s) expressions
          = List.mapM (evalCrepHolExp t) expressions := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : List.mapM (evalCrepHolExp s) xs
                = List.mapM (evalCrepHolExp t) xs :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case8 left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case9 operator args h => simp only [evalCrepHolExp]
  | case10 operator left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case11 operator left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case12 => simp only [evalCrepHolExp, hba]
  | case13 => simp only [evalCrepHolExp, hta]

/-- CakeML's `eval_code_inl` (`crep_inlineProofScript.sml:1513`): if `s` and `t`
    are related by `state_rel_code` with equal locals and `t`'s code inlines
    `s`'s code along `inl_fs`, then every expression `s` evaluates to, `t`
    evaluates to as well. -/
theorem crepInlineEvalCodeInl [NeZero width] [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (s t : CrepHolState (RiscV.Word width) σ) (e : CrepExp (RiscV.Word width))
    (value : RiscV.Word width) (inlFs : CrepInlineFmap (RiscV.Word width))
    (heval : evalCrepHolExp s e = some value)
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    evalCrepHolExp t e = some value := by
  have hsubset := crepInlineCodeInlRel_fdom_subset inlFs s t hcode
  rw [← heval]
  exact (evalCrepHolExp_state_rel_code s t e hstate hlocals hsubset).symm

/-- List-level option-map congruence (the `l1 = l2` case of CakeML's
    `OPT_MMAP_CONG`, `cakeml/misc/miscScript.sml:2481`): pointwise equal
    evaluators give equal `OPT_MMAP`/`mapM` results.  Untagged because the Lean
    evaluator is the fixed-width `evalCrepHolExp` and `mapM` is the
    `List.mapM` carrier rather than HOL `OPT_MMAP`. -/
theorem crepOptMmapEvalCongr [NeZero width]
    (s t : CrepHolState (RiscV.Word width) σ) (es : List (CrepExp (RiscV.Word width)))
    (h : ∀ e ∈ es, evalCrepHolExp s e = evalCrepHolExp t e) :
    es.mapM (evalCrepHolExp s) = es.mapM (evalCrepHolExp t) := by
  induction es with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- CakeML's `opt_mmap_mem_func` (`pan_commonPropsScript.sml:49`): every element
    of a list that `OPT_MMAP` maps to `SOME` is itself mapped to `SOME`. -/
theorem crepOptMmapMemFunc [NeZero width] (s : CrepHolState (RiscV.Word width) σ) :
    ∀ (es : List (CrepExp (RiscV.Word width))) (values : List (RiscV.Word width)),
      es.mapM (evalCrepHolExp s) = some values →
      ∀ e ∈ es, ∃ m, evalCrepHolExp s e = some m := by
  intro es
  induction es with
  | nil => intro values h e he; simp at he
  | cons x xs ih =>
      intro values h e he
      simp only [List.mapM_cons] at h
      cases hx : evalCrepHolExp s x with
      | none => simp [hx] at h
      | some v =>
          cases hxs : xs.mapM (evalCrepHolExp s) with
          | none => simp [hx, hxs] at h
          | some vs =>
              rw [List.mem_cons] at he
              rcases he with rfl | he
              · exact ⟨v, hx⟩
              · exact ih vs hxs e he

/-- CakeML's `opt_mmap_eval_code_inl` (`crep_inlineProofScript.sml:1530`): the
    `eval_code_inl` expression transfer lifted across a whole expression list,
    `OPT_MMAP (eval s) es = SOME vals` implies `OPT_MMAP (eval s1) es = SOME vals`
    under `state_rel_code`, `locals_strong_rel` and `code_inl_rel`.  Untagged:
    fixed-width `evalCrepHolExp`/`List.mapM` versus HOL's polymorphic `eval` and
    `OPT_MMAP`. -/
theorem crepInlineOptMmapEvalCodeInl [NeZero width] [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (s t : CrepHolState (RiscV.Word width) σ) (es : List (CrepExp (RiscV.Word width)))
    (values : List (RiscV.Word width)) (inlFs : CrepInlineFmap (RiscV.Word width))
    (heval : es.mapM (evalCrepHolExp s) = some values)
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    es.mapM (evalCrepHolExp t) = some values := by
  have hsubset := crepInlineCodeInlRel_fdom_subset inlFs s t hcode
  have hpoint : ∀ e ∈ es, evalCrepHolExp s e = evalCrepHolExp t e := by
    intro e he
    obtain ⟨m, hm⟩ := crepOptMmapMemFunc s es values heval e he
    have hse := evalCrepHolExp_state_rel_code s t e hstate hlocals hsubset
    rw [hm] at hse
    rw [hm]
    exact hse
  rw [← crepOptMmapEvalCongr s t es hpoint]
  exact heval

/-! ## Runtime `inline_prog_correct` Skip case

CakeML's `inline_prog_correct` (`crep_inlineProofScript.sml:2301`) is stated over
the clock-based `crepSem$evaluate`.  Lean currently has no port of that
evaluator over the 11-field `CrepHolState`; the closest production evaluator is
the fuel-bounded `evalCrepRuntimeResult` over the 14-field `CrepRuntimeState`.
The relations below are runtime projections of the reviewed `CrepHolState`
relations, and `crepInlineRuntimeSkip` proves the Skip constructor case: from a
source run it derives an existential target run and the post-state relations,
never assuming the target run.  Untagged, because the fuel-bounded evaluator is
not HOL's clock-based `evaluate`. -/

abbrev crepInlineRuntimeStateRelCode (s t : CrepRuntimeState α σ) : Prop :=
  crepInlineStateRelCode s.toHolState t.toHolState

abbrev crepInlineRuntimeLocalsStrongRel (s t : CrepRuntimeState α σ) : Prop :=
  s.locals = t.locals

abbrev crepInlineRuntimeCodeInlRel [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inlFs : CrepInlineFmap α) (s t : CrepRuntimeState α σ) : Prop :=
  crepInlineCodeInlRel inlFs s.toHolState t.toHolState

theorem crepInlineRuntimeSkip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq FunName] [LawfulBEq FunName]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (s s' : CrepRuntimeState α σ) (t : CrepRuntimeState α σ)
    (inlFs : CrepInlineFmap α)
    (hsource : evalCrepRuntimeResult handler primitive (fuel + 1) s .skip =
      some (CrepRuntimeResult.normal, s'))
    (hstate : crepInlineRuntimeStateRelCode s t)
    (hlocals : crepInlineRuntimeLocalsStrongRel s t)
    (hcode : crepInlineRuntimeCodeInlRel inlFs s t) :
    ∃ t',
      evalCrepRuntimeResult handler primitive (fuel + 1) t
          (crepInlineProgFmap inlFs .skip) = some (CrepRuntimeResult.normal, t') ∧
      crepInlineRuntimeStateRelCode s' t' ∧
      crepInlineRuntimeLocalsStrongRel s' t' ∧
      crepInlineRuntimeCodeInlRel inlFs s' t' := by
  have hskip := evalCrepRuntimeResult_skip handler primitive fuel s
  have hs' : s' = s := by
    have hq := hsource.symm.trans hskip
    exact congrArg Prod.snd (Option.some.inj hq)
  rw [hs', crepInlineProgFmap_skip inlFs]
  exact ⟨t, evalCrepRuntimeResult_skip handler primitive fuel t, hstate, hlocals, hcode⟩

/-! ## Width-indexed wrappers for the crep_inline state relations

HOL `crepSem$state` is indexed by the word length, so the exact `state_rel`-family
tags are carried by the `...W` declarations over `CrepHolState (BitVec width) σ`
(with `[NeZero width]`); the generic-`α` relations above stay untagged. -/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_def"]
def crepInlineStateRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineStateRel s t

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_def"]
def crepInlineLocalsRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsRel s t

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_strong_rel_def"]
def crepInlineLocalsStrongRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsStrongRel s t

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_dec_clock"]
theorem crepInlineLocalsRel_decClockW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ)
    (hlocals : crepInlineLocalsRelW s t) (hstate : crepInlineStateRelW s t) :
    crepInlineLocalsRelW (decCrepHolClockW s) (decCrepHolClockW t) ∧
    crepInlineStateRelW (decCrepHolClockW s) (decCrepHolClockW t) := by
  have h := crepInlineLocalsRel_decClock s t hlocals hstate
  simpa only [crepInlineLocalsRelW, crepInlineStateRelW,
    decCrepHolClockW_eq_decCrepHolClock] using h

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_ext_rel_def"]
def crepInlineLocalsExtRelW {width : Nat} [NeZero width] {σ : Type}
    (a b a' b' : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsExtRel a b a' b'

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_code_def"]
def crepInlineStateRelCodeW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineStateRelCode s t

end Flapjack
