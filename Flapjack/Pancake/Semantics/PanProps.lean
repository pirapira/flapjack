import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.PanValueFlatten

/-!
HOL counterpart module for `cakeml/pancake/semantics/panPropsScript.sml`.
The full generated semantic property library is not yet present; this module
starts with the value-well-formedness definition used by PanStructs
`compile_correct`.
-/

namespace Flapjack

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
      further from the HOL Bool statement. -/
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
Exact executable port of HOL `panProps$is_wf_shape_v`
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
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def"]
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

end Flapjack
