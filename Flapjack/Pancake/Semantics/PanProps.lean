import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanSem

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

end Flapjack
