import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.PanValueFlatten
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact

/-!
HOL counterpart module for `cakeml/pancake/semantics/panPropsScript.sml`.
The full generated semantic property library is not yet present; this module
starts with the value-well-formedness definition used by PanStructs
`compile_correct`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-! Equality-based first-match lookup for HOL `ALOOKUP` expressions. Lean's
    production `lookupInfo` intentionally takes `[BEq κ]`; this version keeps
    the HOL equality semantics explicit. -/
def panPropsALookupEq [DecidableEq κ] (key : κ) : List (κ × α) → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if decide (candidate = key) then some value else panPropsALookupEq key entries

theorem panPropsALookupEq_mapValues [DecidableEq κ] (key : κ)
    (entries : List (κ × α)) (convert : α → β) :
    panPropsALookupEq key (entries.map fun (name, value) => (name, convert value)) =
      (panPropsALookupEq key entries).map convert := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨name, value⟩
      by_cases hname : name = key
      · simp [panPropsALookupEq, hname]
      · simp [panPropsALookupEq, hname, ih]

theorem lookupInfo_eq_panPropsALookupEq [BEq κ] [LawfulBEq κ] [DecidableEq κ] (key : κ)
    (entries : List (κ × α)) :
    lookupInfo key entries = panPropsALookupEq key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨name, value⟩
      by_cases hname : name = key
      · simp [lookupInfo, panPropsALookupEq, hname]
      · simp [lookupInfo, panPropsALookupEq, hname, ih]

mutual
  /-- Bool-valued comparison for HOL `is_wf_shape_v_def`, using production
      `lookupInfo`. This is not currently tagged as an exact port: the HOL
      predicate uses HOL equality in `ALOOKUP`, while this declaration's
      lookup semantics are selected by `[BEq String]`; the equality adapter
      lemma only identifies lookup for lawful instances and does not establish
      that the production representation is the same HOL interface. Lean
      `StructInfo` also has an additional `shapedFields` cache absent from HOL.
      The separate Prop-valued convenience predicate in CompileCorrect is
      further from the HOL Bool statement.

      Executable-path disposition (bead `flapjack-4ac.4.4.1`): this value-level
      predicate has no call site on the executable compiler path. The RISC-V
      entrypoints (`compileFlapjackRiscVSourceRuntimeImageChecked` and siblings
      in `Flapjack/RiscV/PipelineDiagnostics.lean`) run `staticCheck`
      (`Flapjack/Pancake/PanStatic.lean:1794`), which checks declared shapes
      (`isWfShape`/`checkShape`/`shapedBased...`), not runtime value validity.
      `panIsWfShapeValueBool` occurs only as a proof-side precondition
      (`panStructEveryValueShapeWfBool`,
      `Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean:614`) over
      locals/globals, and the kernel-checked `panIsWfShapeValueHOL_toHOL`
      already connects it to the HOL-shaped `panIsWfShapeValueHOL`. The
      remaining gap to the exact `isWfShapeValueHOLExact` is the carrier
      (`String`/`StructContextHOL` vs `MlStringHOL`/`StructContextExact`),
      tracked by bead `flapjack-pxn.18.3.5.8`. -/
  def panIsWfShapeValueBool (structs : StructContext) : PanValue α → Bool
    | .word _ => true
    | .rStruct values => panIsWfShapeValuesBool structs values
    | .nStruct name fields =>
        (lookupInfo name structs).isSome &&
          panIsWfShapeValueFieldsBool structs fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panIsWfShapeValuesBool (structs : StructContext) : List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panIsWfShapeValueBool structs value && panIsWfShapeValuesBool structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panIsWfShapeValueFieldsBool (structs : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panIsWfShapeValueBool structs value && panIsWfShapeValueFieldsBool structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! ## Exact `is_wf_shape_v` over the exact `ValueHOL`/`StructContextExact`
    carriers

HOL `panProps$is_wf_shape_v` (`cakeml/pancake/semantics/panPropsScript.sml:24-34`)
is total over the exact `v` datatype (`panSemScript.sml:22`) and a
`(stcname # struct_info) list` context, where `stcname = fldname = mlstring`.
The production `panIsWfShapeValueHOL`/`panIsWfShapeValueBool` above use the
`String`-keyed production carriers, so they are not exact.  `ValueHOL width`
(`PanSem/ValueHOL.lean`, tagged `v`) and `StructContextExact`
(`PanLang/Decl.lean`) are the exact carriers, with `structContextLookupHOL` the
first-match `ALOOKUP` and `isWfShapeValuesHOLExact` the `EVERY` fold.  Direct
original-HOL rows are pinned in `scripts/hol-probes/pan_structs_value_validity_probe.out`
and reproduced by `Flapjack/Test/PanStructsValueValidityParity.lean`. -/

/-- The `MAP SND` view of an exact field list does not increase `sizeOf`. -/
theorem sizeOfValueHOLMapSndLe {width : Nat} [NeZero width]
    (fields : List (MlStringHOL × ValueHOL width)) :
    sizeOf (fields.map Prod.snd) ≤ sizeOf fields := by
  induction fields with
  | nil => simp
  | cons pair pairs ih =>
      obtain ⟨name, value⟩ := pair
      simp only [List.map_cons]
      simp
      omega

/-- The exact field list is strictly smaller than the enclosing `NStruct`
    value. -/
theorem sizeOfValueHOLFieldsLtNStruct {width : Nat} [NeZero width]
    (name : MlStringHOL) (fields : List (MlStringHOL × ValueHOL width)) :
    sizeOf fields < sizeOf (.nStruct name fields : ValueHOL width) := by
  simp
  omega

/-! Exact port of HOL `panProps$is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:24-34`):
    `is_wf_shape_v sctxt (Val v) = T`,
    `is_wf_shape_v sctxt (RStruct vs) = EVERY (is_wf_shape_v sctxt) vs`,
    `is_wf_shape_v sctxt (NStruct nm nm_vs) =`
    `(ALOOKUP sctxt nm <> NONE) /\ EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`.
    Over the exact `ValueHOL width` value carrier and the exact MlString-keyed
    `StructContextExact` context. -/
mutual
  /-- Exact port of HOL `panProps$is_wf_shape_v`.  `structContextLookupHOL` is
      `ALOOKUP`, `isSome` is the Bool rendering of `<> NONE`, and
      `isWfShapeValuesHOLExact` is the `EVERY` fold over `MAP SND`. -/
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def"]
  def isWfShapeValueHOLExact {width : Nat} [NeZero width]
      (context : Flapjack.Pancake.PanLang.StructContextExact) : ValueHOL width → Bool
    | .val _ => true
    | .rStruct values => isWfShapeValuesHOLExact context values
    | .nStruct name fields =>
        (Flapjack.Pancake.PanLang.structContextLookupHOL name context).isSome &&
          isWfShapeValuesHOLExact context (fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by
    all_goals first
      | sizeOf_list_dec
      | decreasing_trivial
      | (have h := sizeOfValueHOLMapSndLe fields
         have h2 := sizeOfValueHOLFieldsLtNStruct name fields
         omega)

  /- `EVERY (is_wf_shape_v sctxt) vs` over an exact value list. -/
  def isWfShapeValuesHOLExact {width : Nat} [NeZero width]
      (context : Flapjack.Pancake.PanLang.StructContextExact) : List (ValueHOL width) → Bool
    | [] => true
    | value :: values =>
        isWfShapeValueHOLExact context value && isWfShapeValuesHOLExact context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Untagged support: the exact value-level well-formedness predicate implies
    that the exact `shape_of` image is well-formed (`is_wf_shape_of_v`
    `panPropsScript.sml:38`). -/
private theorem isWfShapeValueHOLExact_shapeOf_val {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width) :
    isWfShapeValueHOLExact context value = true →
      Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) = true := by
  induction value using isWfShapeValueHOLExact.induct
    (motive2 := fun values =>
      isWfShapeValuesHOLExact context values = true →
        Flapjack.Pancake.PanLang.isWfShapesExactHOL context (values.map shapeOfHOLExact) = true) with
  | case1 value =>
      simp [shapeOfHOLExact]
  | case2 values ih =>
      intro h
      simp only [isWfShapeValueHOLExact.eq_2] at h
      simpa [shapeOfHOLExact, Flapjack.Pancake.PanLang.isWfShapeExactHOL] using ih h
  | case3 name fields _ =>
      simp only [isWfShapeValueHOLExact.eq_3, Bool.and_eq_true]
      intro h
      simpa [shapeOfHOLExact, Flapjack.Pancake.PanLang.isWfShapeExactHOL] using h.1
  | case4 =>
      rfl
  | case5 value values ihValue ihValues =>
      rename_i h
      have hp : isWfShapeValueHOLExact context value = true ∧
          isWfShapeValuesHOLExact context values = true := by
        simpa [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true] using h
      simp only [List.map_cons, Flapjack.Pancake.PanLang.isWfShapesExactHOL.eq_2,
        Bool.and_eq_true]
      exact ⟨ihValue hp.1, ihValues hp.2⟩

/-- Exact port of HOL `panProps$is_wf_shape_of_v`
    (`panPropsScript.sml:38`): `!sctxt v. is_wf_shape_v sctxt v ==>
    is_wf_shape sctxt (shape_of v)`, over the exact `ValueHOL width` value
    carrier and MlString-keyed `StructContextExact` context.  The Bool-valued
    predicates are rendered as `= true`, matching the accepted
    `flattenHOL_length_eq_sizeOfShapeHOL` style; no extra hypotheses. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_of_v"]
theorem isWfShapeValueHOLExact_shapeOfHOLExact {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width)
    (h : isWfShapeValueHOLExact context value = true) :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) = true :=
  isWfShapeValueHOLExact_shapeOf_val context value h

/-- The `MAP SND` view of a field list does not increase `sizeOf`, which
    justifies the well-founded recursion of `panIsWfShapeValueHOL` (HOL's
    `EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`). -/
theorem panSizeOfMapSndLe (fields : List (FieldName × PanValue α)) :
    sizeOf (fields.map Prod.snd) ≤ sizeOf fields := by
  induction fields with
  | nil => simp
  | cons pair pairs ih =>
      obtain ⟨field, value⟩ := pair
      simp only [List.map_cons]
      simp
      omega

/-- The context argument of a struct value is strictly larger in `sizeOf` than
    its field list. -/
theorem sizeOfFieldsLtNStruct (name : StructName)
    (fields : List (FieldName × PanValue α)) :
    sizeOf fields < sizeOf (PanValue.nStruct name fields) := by
  simp
  omega

/-
Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `panProps$is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:24`). The HOL clauses are
    reproduced literally: a scalar is `T`; `RStruct vs` is
    `EVERY (is_wf_shape_v sctxt) vs`; `NStruct nm nm_vs` is
    `(ALOOKUP sctxt nm <> NONE) /\
      EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`.

    `lookupInfo` is the first-match association-list lookup, i.e. the exact
    `alist$ALOOKUP` counterpart, and under `[LawfulBEq String]` its `==`
    reflects HOL's `=`; `isSome` is the Bool rendering of `<> NONE`. The
    context is the HOL-shaped `StructContextHOL` (struct_info `fields` and
    `size` only), so the per-field predicate is `EVERY` over `MAP SND`, as HOL
    has it, rather than a fold over `(FieldName × PanValue)` pairs. The direct
    original-HOL rows are pinned in
    `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/
mutual
  -- FLAPJACK-SPECIFIC (not an exact HOL port): stated over the production
  -- `PanValue` carrier (whose `nStruct` names are `FieldName` = `String`) and a
  -- `StructContextHOL` keyed by `StructName` = `String`, while HOL
  -- `panPropsScript.sml` uses `fldname`/`stcname` = `mlstring`. The exact
  -- MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8` /
  -- `flapjack-0lj`.
  def panIsWfShapeValueHOL [LawfulBEq String] (context : StructContextHOL) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panIsWfShapeValuesHOL context values
    | .nStruct name fields =>
        (lookupInfo name context).isSome &&
          panIsWfShapeValuesHOL context (fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by
    all_goals first
      | sizeOf_list_dec
      | decreasing_trivial
      | (have h := panSizeOfMapSndLe fields
         have h2 := sizeOfFieldsLtNStruct name fields
         omega)

  def panIsWfShapeValuesHOL [LawfulBEq String] (context : StructContextHOL) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panIsWfShapeValueHOL context value && panIsWfShapeValuesHOL context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! ## Adapter to the production cache-augmented struct context

Clause-by-clause relation between the exact HOL-shaped `is_wf_shape_v` port
over `StructContextHOL` and the production `panIsWfShapeValueBool` over the
cache-augmented `StructContext`. The context adapter is the projection
`StructContext.toHOL`, which drops the production-only `shapedFields` cache and
preserves first-match lookup shadowing. -/
mutual
  theorem panIsWfShapeValueHOL_toHOL [LawfulBEq String] (context : StructContext)
      (value : PanValue α) :
      panIsWfShapeValueHOL context.toHOL value = panIsWfShapeValueBool context value := by
    cases value with
    | word word => simp [panIsWfShapeValueHOL, panIsWfShapeValueBool]
    | rStruct values =>
        simp only [panIsWfShapeValueHOL, panIsWfShapeValueBool]
        exact panIsWfShapeValuesHOL_toHOL context values
    | nStruct name fields =>
        simp only [panIsWfShapeValueHOL, panIsWfShapeValueBool, lookupInfo_toHOL_isSome]
        rw [panIsWfShapeValuesHOL_mapSnd_toHOL context fields]

  theorem panIsWfShapeValuesHOL_toHOL [LawfulBEq String] (context : StructContext)
      (values : List (PanValue α)) :
      panIsWfShapeValuesHOL context.toHOL values = panIsWfShapeValuesBool context values := by
    cases values with
    | nil => simp [panIsWfShapeValuesHOL, panIsWfShapeValuesBool]
    | cons value values =>
        simp only [panIsWfShapeValuesHOL, panIsWfShapeValuesBool]
        rw [panIsWfShapeValueHOL_toHOL context value,
          panIsWfShapeValuesHOL_toHOL context values]

  theorem panIsWfShapeValuesHOL_mapSnd_toHOL [LawfulBEq String] (context : StructContext)
      (fields : List (FieldName × PanValue α)) :
      panIsWfShapeValuesHOL context.toHOL (fields.map Prod.snd)
        = panIsWfShapeValueFieldsBool context fields := by
    cases fields with
    | nil => simp [panIsWfShapeValuesHOL, panIsWfShapeValueFieldsBool]
    | cons field fields =>
        obtain ⟨fieldName, value⟩ := field
        simp only [List.map_cons, panIsWfShapeValuesHOL, panIsWfShapeValueFieldsBool]
        rw [panIsWfShapeValueHOL_toHOL context value,
          panIsWfShapeValuesHOL_mapSnd_toHOL context fields]
end

/-- HOL `fdoms_eq_flookup_some_none` (`panPropsScript.sml:276`): if two finite
    maps have the same domain, every defined lookup in the first is also defined
    in the second. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "fdoms_eq_flookup_some_none"]
theorem fdoms_eq_flookup_some_none {α : Type} {β : Type} (fm fm' : FiniteMap α β) (n : α)
    (v : β) (_vPrime : β) (hdom : FDOM fm = FDOM fm') (hv : FLOOKUP fm n = some v) :
    ∃ v', FLOOKUP fm' n = some v' := by
  have hmem : FDOM fm' n := by
    rw [← hdom]
    change fm n ≠ none
    change fm n = some v at hv
    rw [hv]
    exact Option.some_ne_none v
  change fm' n ≠ none at hmem
  cases h' : fm' n with
  | none => rw [h'] at hmem; exact absurd rfl hmem
  | some v' => exact ⟨v', by change fm' n = some v'; rw [h']⟩

/-- HOL `OPT_MMAP_MEM_IMP` (`panPropsScript.sml:115`): if `OPT_MMAP f xs` succeeds
    with `ys`, every element of `ys` is the image under `f` of an element of `xs`.
    Pure option/list lemma (no Boolean key-equality carrier); `List.mapM` is the
    repository's documented `OPT_MMAP` carrier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_MEM_IMP"]
theorem OPT_MMAP_MEM_IMP {α : Type} {β : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (y : β) (h : xs.mapM f = some ys) (hy : y ∈ ys) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil] at h
      change some [] = some ys at h
      rw [Option.some.injEq] at h
      subst h
      simp at hy
  | cons a as ih =>
      rw [List.mapM_cons] at h
      change (Option.bind (f a) (fun b => Option.bind (as.mapM f) (fun rest => some (b :: rest)))) = some ys at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨b, hfa, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨rest, hta, h⟩ := h
      change some (b :: rest) = some ys at h
      rw [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hy with hyb | hyr
      · subst hyb
        exact ⟨a, List.mem_cons_self, hfa⟩
      · obtain ⟨x, hx, hfx⟩ := ih rest hta hyr
        exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- Cake `list_rel_flatten_with_shape_length`
    (`cakeml/pancake/semantics/panPropsScript.sml:549`), a prerequisite of the
    PanToCrep Call case `call_preserve_state_code_locals_rel`
    (`pan_to_crepProofScript.sml:2440`):

    `LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
     size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
     EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
     LIST_REL (\sh arg. sh = shape_of arg) sh args /\
     EVERY is_wf_shape_v_nil args ==>
     LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)`.

    Representation notes (why this is not `@[hol]`-tagged): Cake's `LIST_REL`
    (`shapes` paired pointwise with `args`) is rendered here as the indexed
    `List.get` equality (the toolchain in this repository does not expose
    `List.Forall₂`); `EL n args = v` is the indexed `arguments[n]'hn = value`;
    `flat`/`with_shape`/`size_of_shape`/`shape_of`/`is_wf_shape_v_nil` are
    `panValueFlatten`/`withShape`/`Shape.shapeSize`/`panValueShape`/
    `panValueIsWf []` respectively. -/
theorem listRelFlattenWithShapeLength (shapes : List Shape) (names : List Nat)
    (arguments : List (PanValue α)) (value : PanValue α) (n : Nat)
    (hnames : names.length = (arguments.map panValueFlatten).flatten.length)
    (hsize : Shape.shapeSize (.comb shapes) =
      (arguments.map panValueFlatten).flatten.length)
    (hn : n < arguments.length)
    (hget : arguments[n]'hn = value)
    (hlen : arguments.length = shapes.length)
    (hrel : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes.get ⟨i, hsi⟩ =
        panValueShape ([] : StructContext) (arguments.get ⟨i, hai⟩))
    (hwf : arguments.all
      (fun argument => panValueIsWf ([] : StructContext) argument) = true) :
    ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length =
      (panValueFlatten value).length := by
  have hvalues : names.length = Shape.shapeSize (.comb shapes) :=
    hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hshape : shapes[n]'hnshapes = panValueShape ([] : StructContext) value := by
    have h := hrel n hnshapes hn
    rw [List.get_eq_getElem, List.get_eq_getElem] at h
    rw [hget] at h
    exact h
  have hwfval : panValueIsWf ([] : StructContext) value = true := by
    have hall := List.all_eq_true.mp hwf
    exact hall value (by rw [← hget]; exact List.getElem_mem hn)
  have hflat := panValueFlatten_length_eq_shapeSize value
    (panValueIsWf_isWfShape_panValueShape ([] : StructContext) value hwfval)
  rw [withShape_getElem_length shapes names n hvalues hnshapes, hshape]
  exact hflat.symm

/-- Flattening offset helper: the `n'`-th element of the `n`-th group of a
    list-of-lists is the element at the sum of the preceding group lengths plus
    `n'`. -/
theorem getElem?_flatten_take_sum {α : Type} {l : List (List α)} {n n' : Nat}
    (hn : n < l.length) (hn' : n' < (l[n]'hn).length) :
    l.flatten[((l.take n).map List.length).sum + n']? = (l[n]'hn)[n']? := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a rest ih =>
      cases n with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
            List.flatten_cons, List.getElem_cons_zero] at hn' ⊢
          rw [List.getElem?_append, if_pos hn']
      | succ k =>
          rw [List.take_cons (Nat.succ_pos k), Nat.succ_sub_one]
          simp only [List.map_cons, List.sum_cons, List.flatten_cons,
            List.getElem_cons_succ] at hn' ⊢
          rw [List.getElem?_append, if_neg (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
          exact ih (n := k) (by simpa using hn) (by simpa using hn')

/-- Port of Cake `list_rel_flatten_with_shape_flookup`
    (`cakeml/pancake/semantics/panPropsScript.sml:585`), a prerequisite of the
    Pan-to-Crep Call case.  Representation differences (documented, no exact
    HOL tag): HOL `LIST_REL`/`shape_of`/`is_wf_shape_v_nil`/`EL` are rendered
    here as the indexed `get` equality, `panValueShape []`, `panValueIsWf []`
    and `getElem`; HOL `FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))` is
    `FUPDATE_LIST FEMPTY (names.zip ((arguments.map panValueFlatten).flatten))`. -/
theorem listRelFlattenWithShapeFlookup (shapes : List Shape) (names : List Nat)
    (arguments : List (PanValue α)) (value : PanValue α) (n n' : Nat)
    (hdistinct : names.Nodup)
    (hnames : names.length = (arguments.map panValueFlatten).flatten.length)
    (hsize : Shape.shapeSize (.comb shapes) = (arguments.map panValueFlatten).flatten.length)
    (hn : n < arguments.length)
    (hget : arguments[n]'hn = value)
    (hlen : arguments.length = shapes.length)
    (hrel : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes.get ⟨i, hsi⟩ = panValueShape ([] : StructContext) (arguments.get ⟨i, hai⟩))
    (hwf : arguments.all (fun argument => panValueIsWf ([] : StructContext) argument) = true)
    (hgroup : ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length =
      (panValueFlatten value).length)
    (hn' : n' < ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length) :
    FLOOKUP (FUPDATE_LIST FEMPTY (names.zip ((arguments.map panValueFlatten).flatten)))
        (((withShape shapes names)[n]'(by rw [withShape_length]; omega))[n']'hn') =
      some ((panValueFlatten value)[n']'(by rw [← hgroup]; exact hn')) := by
  have hvalues : names.length = Shape.shapeSize (.comb shapes) := hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hgroupSize : Shape.shapeSize (shapes[n]'hnshapes) = (panValueFlatten value).length :=
    (withShape_getElem_length shapes names n hvalues hnshapes).symm.trans hgroup
  have hn'val : n' < (panValueFlatten value).length := by rw [← hgroup]; exact hn'
  have hident : Shape.shapeSize (.comb (shapes.take n)) =
      ((arguments.take n).map panValueFlatten).flatten.length := by
    apply shapeSize_comb_eq_flatten_length_of_getElem (shapes.take n) (arguments.take n)
    · rw [List.length_take, List.length_take, hlen]
    · intro i hi
      have hin : i < n := Nat.lt_of_lt_of_le hi (List.length_take_le n arguments)
      have hians : i < arguments.length := by omega
      have hish : i < shapes.length := by omega
      rw [List.getElem?_take, if_pos hin, List.getElem?_take, if_pos hin,
        List.getElem?_eq_some_iff.mpr ⟨hish, rfl⟩,
        List.getElem?_eq_some_iff.mpr ⟨hians, rfl⟩]
      simp only [Option.map_some]
      have hr := hrel i hish hians
      rw [List.get_eq_getElem, List.get_eq_getElem] at hr
      rw [hr]
    · intro arg hmem
      have hall := List.all_eq_true.mp hwf arg (List.mem_of_mem_take hmem)
      exact panValueIsWf_isWfShape_panValueShape ([] : StructContext) arg hall
  have hboundSize : Shape.shapeSize (.comb (shapes.take n)) + n' <
      Shape.shapeSize (.comb shapes) := by
    have hsplit := shapeSize_comb_append (shapes.take n) (shapes.drop n)
    rw [List.take_append_drop] at hsplit
    have hdrop := shapeSize_drop_head_le shapes n hnshapes
    omega
  have hbound : Shape.shapeSize (.comb (shapes.take n)) + n' < names.length := by
    rw [hnames, ← hsize]; exact hboundSize
  have hbound' : Shape.shapeSize (.comb (shapes.take n)) + n' <
      (arguments.map panValueFlatten).flatten.length := by rw [← hnames]; exact hbound
  have hgroupElem :
      ((withShape shapes names)[n]'(by rw [withShape_length]; omega))[n']'hn' =
        names[Shape.shapeSize (.comb (shapes.take n)) + n']'hbound := by
    rw [withShape_getElem_getElem shapes names n n' hvalues hnshapes
      (by rw [hgroupSize]; exact hn'val) hn']
  have hflat? : ((arguments.map panValueFlatten).flatten)[
      Shape.shapeSize (.comb (shapes.take n)) + n']? = (panValueFlatten value)[n']? := by
    rw [hident, List.length_flatten, List.map_take,
      getElem?_flatten_take_sum (l := arguments.map panValueFlatten) (n := n) (n' := n')
        (by rw [List.length_map]; exact hn) (by rw [List.getElem_map, hget]; exact hn'val)]
    rw [List.getElem_map, hget]
  have hflatElem : ((arguments.map panValueFlatten).flatten)[
      Shape.shapeSize (.comb (shapes.take n)) + n']'hbound' =
      (panValueFlatten value)[n']'(by rw [← hgroup]; exact hn') := by
    have hsome : ((arguments.map panValueFlatten).flatten)[
        Shape.shapeSize (.comb (shapes.take n)) + n']? =
        some ((panValueFlatten value)[n']'(by rw [← hgroup]; exact hn')) := by
      rw [hflat?, List.getElem?_eq_some_iff.mpr ⟨by rw [← hgroup]; exact hn', rfl⟩]
    obtain ⟨_, hfe⟩ := List.getElem?_eq_some_iff.mp hsome
    exact hfe
  rw [hgroupElem]
  exact (FLOOKUP_FUPDATE_LIST_zip_getElem names ((arguments.map panValueFlatten).flatten)
    FEMPTY (Shape.shapeSize (.comb (shapes.take n)) + n') hdistinct hnames hbound).trans
    (congrArg some hflatElem)

/-- Exact port of HOL `all_distinct_alist_no_overlap`
    (`cakeml/pancake/semantics/panPropsScript.sml:476`): a duplicate-free slot
    list laid out by `withShape` makes the zipped finite map overlap-free.
    HOL `alist_to_fmap (ZIP (vs, ZIP (sh, with_shape sh ns)))` is Lean's
    right-folded `alistToFmap`, including when `vs` contains duplicates. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_no_overlap"]
theorem allDistinctAlistNoOverlap {α : Type} [BEq α] [LawfulBEq α]
    (sh : List Shape) (ns : List Nat) (vs : List α)
    (hdistinct : ns.Nodup) (hlen1 : ns.length = Shape.shapeSize (.comb sh))
    (hlen2 : vs.length = sh.length) :
    noOverlap (alistToFmap (vs.zip (sh.zip (withShape sh ns)))) := by
  constructor
  · intro x a xs hlk
    obtain ⟨e, hmem, hke, hve⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) x (a, xs) hlk
    have he : e = (x, (a, xs)) := Prod.ext hke hve
    subst he
    obtain ⟨n, hn, _hj, _hfst, hsnd⟩ :=
      mem_zip_getElem vs (sh.zip (withShape sh ns)) (x, (a, xs)) hmem
    have hnsh : n < sh.length := by rw [← hlen2]; exact hn
    have hz := hsnd
    rw [List.getElem_zip] at hz
    have hshapeget :
        (withShape sh ns)[n]'(by rw [withShape_length]; exact hnsh) = xs :=
      congrArg Prod.snd hz
    exact hshapeget ▸ all_distinct_withShape sh ns n hdistinct hnsh hlen1
  · intro x y a b xs ys hx hy hinter
    rcases hinter with ⟨z, hzxs, hzys⟩
    obtain ⟨e, hme, hke, hve⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) x (a, xs) hx
    obtain ⟨f, hmf, hkf, hvf⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) y (b, ys) hy
    have he : e = (x, (a, xs)) := Prod.ext hke hve
    subst he
    have hf : f = (y, (b, ys)) := Prod.ext hkf hvf
    subst hf
    by_cases hxy : x = y
    · exact hxy
    · have hdisj :=
        listDisjoint_of_mem_zip_withShape vs sh ns (x, (a, xs)) (y, (b, ys))
          hlen2 (by rw [withShape_length]) hdistinct hlen1 hme hmf hxy
      exact (hdisj z hzxs hzys).elim


/-- Exact port of HOL `all_distinct_alist_ctxt_max`
    (`cakeml/pancake/semantics/panPropsScript.sml:517`): every slot recorded in
    the compiled context is bounded by `MAX_LIST ns`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_ctxt_max"]
theorem allDistinctAlistCtxtMax {α : Type} [BEq α] [LawfulBEq α]
    (sh : List Shape) (ns : List Nat) (vs : List α)
    (_hdistinct : ns.Nodup) (hlen1 : ns.length = Shape.shapeSize (.comb sh))
    (hlen2 : vs.length = sh.length) :
    ctxtMax (maxList ns) (alistToFmap (vs.zip (sh.zip (withShape sh ns)))) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro v a xs hlk x hx
  obtain ⟨e, hmem, hke, hve⟩ :=
    flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) v (a, xs) hlk
  have he : e = (v, (a, xs)) := Prod.ext hke hve
  subst he
  obtain ⟨n, hn, _hj, _hfst, hsnd⟩ :=
    mem_zip_getElem vs (sh.zip (withShape sh ns)) (v, (a, xs)) hmem
  have hnsh : n < sh.length := by rw [← hlen2]; exact hn
  have hz := hsnd
  rw [List.getElem_zip] at hz
  have hshapeget :
      (withShape sh ns)[n]'(by rw [withShape_length]; exact hnsh) = xs :=
    congrArg Prod.snd hz
  have hxmem : x ∈ ns := by
    rw [← hshapeget] at hx
    exact mem_of_withShape_mem sh ns n x (by rw [withShape_length]; exact hnsh) hlen1 hx
  exact maxList_ge_of_mem ns x hxmem

/-! ## Exact `res_var` / `shape_of` lemmas over the exact carriers

`panPropsScript.sml` states four small properties of HOL `shape_of`
(`panPropsScript.sml:14`) and `res_var` (`panPropsScript.sml:220-240`) over the
exact `panSem` carriers.  The exact Lean counterparts are `shapeOfHOLExact`
(`PanSem/ValueHOL.lean`, tagged `shape_of_def`) and `resVarHOLExact`
(`PanSem/LocalUpdatesExact.lean`, tagged `res_var_def`), so these lemmas are
ported over those definitions rather than the production generic carriers used
by the `panValueShape`/`panValueResVar` bridges. -/

/-- Exact port of HOL `panProps$shape_of_val` (`panPropsScript.sml:14`):
    `shape_of (Val x) = One`.  The `Val` payload is ignored, so the
    `HolWordLab` carrier does not affect the result. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "shape_of_val"]
theorem shapeOfHOLExact_val {width : Nat} [NeZero width] (value : HolWordLab width) :
    shapeOfHOLExact (.val value : ValueHOL width) =
      Flapjack.Pancake.PanLang.ShapeHOL.one := by
  simp [shapeOfHOLExact]

/-- Function-backed rendering of HOL `panProps$FLOOKUP_pan_res_var_thm`
    (`panPropsScript.sml:236`). Untagged because HOL's `lc` is a finite map,
    while this Lean statement quantifies over every `MlS → Option _` function. -/
theorem resVarHOLExact_flookup {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (m n : MlS) (v : Option (ValueHOL width)) :
    resVarHOLExact locals (m, v) n = if n = m then v else locals n := by
  rcases v with _ | value <;> simp [resVarHOLExact]

/-- Function-backed rendering of HOL `panProps$flookup_res_var_diff_eq_org`
    (`panPropsScript.sml:228`); untagged because its lookup-function input
    ranges beyond HOL finite maps. -/
theorem resVarHOLExact_flookup_of_ne {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (n m : MlS) (v : Option (ValueHOL width)) (h : n ≠ m) :
    resVarHOLExact locals (n, v) m = locals m := by
  have h' : m ≠ n := fun hm => h hm.symm
  rcases v with _ | value <;> simp [resVarHOLExact, h']

/-- Function-backed rendering of HOL `panProps$flookup_res_var_some_eq_lookup`
    (`panPropsScript.sml:220`); untagged because the two lookup-function
    arguments range beyond HOL finite maps. -/
theorem resVarHOLExact_flookup_some_eq_lookup {width : Nat} [NeZero width]
    (lc lc' : MlS → Option (ValueHOL width))
    (v : MlS) (value : ValueHOL width)
    (h : resVarHOLExact lc (v, lc' v) v = some value) : lc' v = some value := by
  cases hv : lc' v with
  | none => simp [resVarHOLExact, hv] at h
  | some w =>
      have hw : some w = some value := by simpa [resVarHOLExact, hv] using h
      exact hw

/-! ## Exact `size_of_sh_with_ctxt_eq` over the exact carriers

`panPropsScript.sml:184` states that a shape that is well-formed under the empty
struct context has the same size with or without a context.  The exact Lean
counterparts are `sizeOfShapeWithContextHOL` (tagged `size_of_sh_with_ctxt_def`)
and `sizeOfShapeHOL` (tagged `size_of_shape_def`) over `ShapeHOL`, with the
context-less well-formedness rendered as `isWfShapeExactHOL [] shape = true`
(HOL `is_wf_shape_nil` is the overload `is_wf_shape []`). -/

open Flapjack.Pancake.PanLang

/- Untagged support: context-free well-formed shapes have the same
    with-context size as their plain `size_of_shape` size, for every context. -/
mutual
  theorem sizeOfShapeWithContextHOL_eq_nil : ∀ (shape : ShapeHOL),
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ context, sizeOfShapeWithContextHOL context shape = sizeOfShapeHOL shape
    | .one, _ => by simp
    | .comb shapes, h => by
        simp only [isWfShapeExactHOL_comb] at h
        intro context
        simp [sizeOfShapeWithContextHOL_comb, sizeOfShapeHOL_comb,
          sizeOfShapesWithContextHOL_eq_nil shapes h context]
    | .named name, h => by
        simp [isWfShapeExactHOL_named, structContextLookupHOL_nil] at h
  theorem sizeOfShapesWithContextHOL_eq_nil : ∀ (shapes : List ShapeHOL),
      isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      ∀ context, sizeOfShapesWithContextHOL context shapes = sizeOfShapesHOL shapes
    | [], _ => by simp
    | shape :: shapes, h => by
        simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        intro context
        simp [sizeOfShapesWithContextHOL_cons, sizeOfShapesHOL_cons,
          sizeOfShapeWithContextHOL_eq_nil shape h.1 context,
          sizeOfShapesWithContextHOL_eq_nil shapes h.2 context]
end

/-- Exact port of HOL `panProps$size_of_sh_with_ctxt_eq`
    (`panPropsScript.sml:184`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "size_of_sh_with_ctxt_eq"]
theorem sizeOfShapeWithContextHOL_eq (shape : ShapeHOL) (context : StructContextExact)
    (h : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    sizeOfShapeWithContextHOL context shape = sizeOfShapeHOL shape :=
  sizeOfShapeWithContextHOL_eq_nil shape h context

/-! ## Exact `length_flatten_eq_size_of_shape` over the exact carriers

`panPropsScript.sml:171` states that a value whose `shape_of` is well-formed under
the empty struct context has `LENGTH (flatten v) = size_of_shape (shape_of v)`.
The exact Lean counterparts are `flattenHOL` (tagged `flatten_def`),
`shapeOfHOLExact` (tagged `shape_of_def`), and `sizeOfShapeHOL` (tagged
`size_of_shape_def`) over `ValueHOL`, with the context-less well-formedness
rendered as `isWfShapeExactHOL [] shape = true` (HOL `is_wf_shape_nil` is the
overload `is_wf_shape []`). -/

/- Untagged support: the flattened word list of a value has length equal to the
    plain `size_of_shape` size of its shape, for values whose shape is
    well-formed under the empty struct context. -/
mutual
  theorem lengthFlattenHOL_eq_sizeOfShapeHOL {width : Nat} [NeZero width]
      : ∀ (v : ValueHOL width),
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true →
        (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v)
    | .val w, _ => by simp [flattenHOL, shapeOfHOLExact]
    | .rStruct fields, h => by
        simp only [shapeOfHOLExact, isWfShapeExactHOL_comb] at h
        simp only [flattenHOL, shapeOfHOLExact, sizeOfShapeHOL_comb]
        exact lengthFlattenHOLs_eq_sizeOfShapesHOL fields h
    | .nStruct name fields, h => by
        simp [shapeOfHOLExact, isWfShapeExactHOL_named, structContextLookupHOL_nil] at h
  theorem lengthFlattenHOLs_eq_sizeOfShapesHOL {width : Nat} [NeZero width]
      : ∀ (vs : List (ValueHOL width)),
        isWfShapesExactHOL ([] : StructContextExact) (vs.map shapeOfHOLExact) = true →
        (vs.map flattenHOL).flatten.length = sizeOfShapesHOL (vs.map shapeOfHOLExact)
    | [], _ => by simp
    | v :: vs, h => by
        simp only [List.map_cons, isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        have h1 := lengthFlattenHOL_eq_sizeOfShapeHOL v h.1
        have h2 := lengthFlattenHOLs_eq_sizeOfShapesHOL vs h.2
        simp [List.flatten_cons, List.length_append, h1, h2]
end

/-- Exact port of HOL `panProps$length_flatten_eq_size_of_shape`
    (`panPropsScript.sml:171`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "length_flatten_eq_size_of_shape"]
theorem flattenHOL_length_eq_sizeOfShapeHOL {width : Nat} [NeZero width]
    (v : ValueHOL width)
    (h : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v) :=
  lengthFlattenHOL_eq_sizeOfShapeHOL v h

/-! ## Exact `functions` append/filter lemmas over the exact declaration carrier

`panPropsScript.sml:1496-1516` groups three list identities about the
`panLang$functions` projection and the `is_function`/`is_decl` predicates.  The
exact Lean counterparts are `functionsHOL` (tagged `functions_def`),
`isDeclHOL` (tagged `is_decl_def`) and `isFunctionHOL` (tagged
`is_function_def`), all over the reviewed `List (DeclHOL width)` carrier, so
these statements transfer clause for clause with no extra hypotheses.  HOL's
`functions_eq_FILTER` (`panPropsScript.sml:1487`, bead `flapjack-4ac.4.80`) is
deliberately excluded: its `MAP` carries an `ARB` fallback whose rendering is
not yet reviewed (see `functions_eq_filterMap` in `Flapjack/Pancake/PanSimp.lean`
and the note in `Flapjack/Pancake/Proofs/PanGlobals.lean`). -/

/-- Exact port of HOL `panProps$functions_append`
    (`panPropsScript.sml:1496`): the function table of a concatenation is the
    concatenation of the function tables. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_append"]
theorem functionsHOL_append {width : Nat} [NeZero width]
    (prog1 prog2 : List (DeclHOL width)) :
    functionsHOL (prog1 ++ prog2) = functionsHOL prog1 ++ functionsHOL prog2 := by
  induction prog1 with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;> simp [functionsHOL, ih]

/-- Exact port of HOL `panProps$functions_FILTER`
    (`panPropsScript.sml:1502`): filtering a program to its function
    declarations leaves the function table unchanged. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER"]
theorem functionsHOL_filter_isFunction {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    functionsHOL (prog.filter isFunctionHOL) = functionsHOL prog := by
  induction prog with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [functionsHOL, isFunctionHOL, List.filter_cons, ih]

/-- Exact port of HOL `panProps$functions_FILTER'`
    (`panPropsScript.sml:1510`): a program filtered to its value declarations
    has an empty function table. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER'"]
theorem functionsHOL_filter_isDecl {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    functionsHOL (prog.filter isDeclHOL) = [] := by
  induction prog with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [functionsHOL, isDeclHOL, List.filter_cons, ih]

end Flapjack
