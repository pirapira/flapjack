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
  /-- Bool-valued counterpart of HOL `is_wf_shape_v_def`, using production
      `lookupInfo`. Its `LawfulBEq String` instance identifies lookup with
      HOL equality-based `ALOOKUP` (see
      `lookupInfo_eq_panPropsALookupEq`). Lean `StructInfo` has an additional
      `shapedFields` cache absent from HOL; this predicate ignores it. -/
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def"]
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

end Flapjack
