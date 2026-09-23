import Flapjack.PanValues
import Flapjack.Pancake.PanStatic

namespace Flapjack

mutual
  /-- Counterpart of Cake's `flatten` (`cakeml/pancake/semantics/panSemScript.sml:388-391`):
      a scalar flattens to its single word, a record concatenates the flattened
      values of its fields, and a named record concatenates the flattened values of
      the values of its fields. -/
  def panValueFlatten : PanValue α → List α
    | .word value => [value]
    | .rStruct fields => panValueFlattenValues fields
    | .nStruct _ fields => panValueFlattenFields fields
  termination_by value => sizeOf value
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValueFlattenValues : List (PanValue α) → List α
    | [] => []
    | value :: values => panValueFlatten value ++ panValueFlattenValues values
  termination_by values => sizeOf values
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValueFlattenFields : List (FieldName × PanValue α) → List α
    | [] => []
    | (_, value) :: fields => panValueFlatten value ++ panValueFlattenFields fields
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem panValueFlatten_word (value : α) :
    panValueFlatten (α := α) (.word value) = [value] := by simp [panValueFlatten]

theorem panValueFlatten_rStruct (fields : List (PanValue α)) :
    panValueFlatten (α := α) (.rStruct fields) = panValueFlattenValues fields := by
  simp [panValueFlatten]

theorem panValueFlatten_nStruct (name : StructName) (fields : List (FieldName × PanValue α)) :
    panValueFlatten (α := α) (.nStruct name fields) = panValueFlattenFields fields := by
  simp [panValueFlatten]

theorem panValueFlattenValues_eq_flatMap (values : List (PanValue α)) :
    panValueFlattenValues values = values.flatMap panValueFlatten := by
  induction values with
  | nil => simp [panValueFlattenValues]
  | cons value values ih => simp [panValueFlattenValues, ih]

theorem panValueFlattenFields_eq_flatMap (fields : List (FieldName × PanValue α)) :
    panValueFlattenFields fields = (fields.map Prod.snd).flatMap panValueFlatten := by
  induction fields with
  | nil => simp [panValueFlattenFields]
  | cons field fields ih => obtain ⟨name, value⟩ := field; simp [panValueFlattenFields, ih]

theorem shapeSize_comb_eq_sum (shapes : List Shape) :
    Shape.shapeSize (.comb shapes) = (shapes.map Shape.shapeSize).sum := by
  rw [Shape.shapeSize, List.sum_eq_foldl, List.foldl_map]

/-- Counterpart of Cake's `length_flatten_eq_size_of_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:171`): a well-formed value
    flattens to exactly as many words as its shape's size. -/
theorem panValueFlatten_length_eq_shapeSize (value : PanValue α)
    (h : isWfShape ([] : StructContext) (panValueShape ([] : StructContext) value) = true) :
    (panValueFlatten value).length =
      Shape.shapeSize (panValueShape ([] : StructContext) value) := by
  refine (panValueFlatten.induct
    (fun value => isWfShape [] (panValueShape [] value) = true →
      (panValueFlatten value).length = Shape.shapeSize (panValueShape [] value))
    (fun fields => isWfShape.isWfShapeList [] (fields.map (fun p => panValueShape [] p.2)) = true →
      (panValueFlattenFields fields).length =
        (fields.map (fun p => Shape.shapeSize (panValueShape [] p.2))).sum)
    (fun values => isWfShape.isWfShapeList [] (values.map (panValueShape [])) = true →
      (panValueFlattenValues values).length =
        (values.map (fun v => Shape.shapeSize (panValueShape [] v))).sum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_) value h
  · intro _
    simp [panValueFlatten, panValueShape]
  · intro fields ih hwf
    rw [panValueShape.eq_def] at hwf
    simp only [isWfShape.eq_def] at hwf
    simp only [panValueFlatten, panValueShape]
    rw [ih hwf, shapeSize_comb_eq_sum, List.map_map]
    rfl
  · intro name fields ih hwf
    rw [panValueShape.eq_def] at hwf
    simp [isWfShape, lookupInfo] at hwf
  · intro _
    simp [panValueFlattenFields]
  · intro fst value fields ihValue ihFields hwf
    simp only [List.map_cons] at hwf
    rw [isWfShape.isWfShapeList.eq_def] at hwf
    simp only [Bool.and_eq_true] at hwf
    simp only [panValueFlattenFields, List.length_append, List.map_cons, List.sum_cons]
    rw [ihValue hwf.1, ihFields hwf.2]
  · intro _
    simp [panValueFlattenValues]
  · intro value values ihValue ihValues hwf
    simp only [List.map_cons] at hwf
    rw [isWfShape.isWfShapeList.eq_def] at hwf
    simp only [Bool.and_eq_true] at hwf
    simp only [panValueFlattenValues, List.length_append, List.map_cons, List.sum_cons]
    rw [ihValue hwf.1, ihValues hwf.2]

/-- Counterpart of Cake's `list_rel_length_shape_of_flatten`
    (`cakeml/pancake/semantics/panPropsScript.sml:256`): for a well-formed list
    of values, the size of the combined shape of their shapes equals the length
    of their concatenated flattenings. -/
theorem shapeSize_comb_map_panValueShape_eq_flatten_length (values : List (PanValue α))
    (hwf : ∀ value, value ∈ values →
      isWfShape ([] : StructContext) (panValueShape ([] : StructContext) value) = true) :
    Shape.shapeSize (.comb (values.map (panValueShape ([] : StructContext)))) =
      (values.map panValueFlatten).flatten.length := by
  induction values with
  | nil => simp [Shape.shapeSize]
  | cons value values ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rw [shapeSize_comb_cons,
      panValueFlatten_length_eq_shapeSize value (hwf value (by simp)),
      ih (fun other hmem => hwf other (by simp [hmem]))]

/-- Flapjack-specific helper using the older context-parameter shape function.
    The exact HOL `flatten_nil_no_size` port uses the source-semantics
    `shape_of` counterpart and lives in `Proofs/PanToCrep.lean`. -/
theorem panValueFlatten_eq_nil_iff_shapeSize_eq_zero (value : PanValue α)
    (h : isWfShape ([] : StructContext) (panValueShape ([] : StructContext) value) = true) :
    panValueFlatten value = [] ↔ Shape.shapeSize (panValueShape ([] : StructContext) value) = 0 := by
  have hlen := panValueFlatten_length_eq_shapeSize value h
  constructor
  · intro hempty
    rw [← hlen, hempty]
    rfl
  · intro hzero
    rw [List.eq_nil_iff_length_eq_zero, hlen, hzero]

/-- Counterpart of Cake's `is_wf_shape_nil_length_flatten`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2469`): a list is a valid
    flattening of a well-formed value when it is empty at shape size zero and
    the flattening at positive shape size, hence its length is the shape size. -/
theorem shapeSize_eq_zero_or_flatten_length (value : PanValue α) (values : List α)
    (hwf : isWfShape ([] : StructContext) (panValueShape ([] : StructContext) value) = true)
    (hnil : Shape.shapeSize (panValueShape ([] : StructContext) value) = 0 → values = [])
    (hpos : 0 < Shape.shapeSize (panValueShape ([] : StructContext) value) →
      values = panValueFlatten value) :
    values.length = Shape.shapeSize (panValueShape ([] : StructContext) value) := by
  by_cases hzero : Shape.shapeSize (panValueShape ([] : StructContext) value) = 0
  · rw [hnil hzero, hzero]
    rfl
  · have hpositive : 0 < Shape.shapeSize (panValueShape ([] : StructContext) value) :=
      Nat.pos_of_ne_zero hzero
    rw [hpos hpositive, panValueFlatten_length_eq_shapeSize value hwf]

/-- Counterpart of Cake's `list_rel_length_shape_of_flatten_better`
    (`cakeml/pancake/semantics/panPropsScript.sml:244`): the pointwise
    shape-relation form of `shapeSize_comb_map_panValueShape_eq_flatten_length`,
    where the shape list is related to the value list entrywise rather than
    being its image. -/
theorem shapeSize_comb_eq_flatten_length_of_getElem (vshs : List Shape)
    (args : List (PanValue α)) (hlen : vshs.length = args.length)
    (hrel : ∀ i, i < args.length →
      vshs[i]? = (args[i]?).map (panValueShape ([] : StructContext)))
    (hwf : ∀ arg, arg ∈ args →
      isWfShape ([] : StructContext) (panValueShape ([] : StructContext) arg) = true) :
    Shape.shapeSize (.comb vshs) = (args.map panValueFlatten).flatten.length := by
  induction args generalizing vshs with
  | nil =>
    cases vshs with
    | nil => simp [Shape.shapeSize]
    | cons sh shs => simp at hlen
  | cons arg args ih =>
    cases vshs with
    | nil => simp at hlen
    | cons vsh vshs =>
      have hhead : vsh = panValueShape ([] : StructContext) arg := by
        have h0 := hrel 0 (by simp)
        simp only [List.getElem?_cons_zero, Option.map_some] at h0
        exact Option.some.inj h0
      have hlenTail : vshs.length = args.length := by simpa using hlen
      have hrelTail : ∀ i, i < args.length →
          vshs[i]? = (args[i]?).map (panValueShape ([] : StructContext)) := by
        intro i hi
        have h := hrel (i + 1) (by simp [hi])
        simpa [List.getElem?_cons_succ] using h
      have hwfTail : ∀ other, other ∈ args →
          isWfShape [] (panValueShape [] other) = true :=
        fun other hmem => hwf other (by simp [hmem])
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [shapeSize_comb_cons, hhead,
        panValueFlatten_length_eq_shapeSize arg (hwf arg (by simp)),
        ih vshs hlenTail hrelTail hwfTail]

end Flapjack
