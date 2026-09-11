import Flapjack.PanValues

/-!
Inversion lemmas for flat word-record shapes.  A successful shape match with a
flat list of `Shape.one`s forces the value to be an anonymous record whose
fields are all words.  This is the source-side destination invariant needed by
the structured assignment correctness constructor.
-/

namespace Flapjack

theorem panValueShape_matches_one_inv
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (value : PanValue α)
    (hshape : panShapeMatches (panValueShape structs value) .one = true) :
    ∃ word, value = .word word := by
  cases value with
  | word word => exact ⟨word, rfl⟩
  | rStruct fields =>
      simp [panValueShape, panShapeMatches] at hshape
  | nStruct name fields =>
      simp [panValueShape, panShapeMatches] at hshape

theorem panValueShape_matches_word_record_inv
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (value : PanValue α) (values : List α)
    (hshape : panShapeMatches (panValueShape structs value)
      (.comb (values.map (fun _ => .one))) = true) :
    ∃ oldValues : List α,
      value = .rStruct (oldValues.map (fun value => .word value)) ∧
      oldValues.length = values.length := by
  cases value with
  | word word =>
      simp [panValueShape, panShapeMatches] at hshape
  | nStruct name fields =>
      simp [panValueShape, panShapeMatches] at hshape
  | rStruct fields =>
      induction fields generalizing values with
      | nil =>
          cases values with
          | nil => exact ⟨[], rfl, rfl⟩
          | cons value values =>
              simp [panValueShape, panShapeMatches,
                panShapeMatches.panShapeListMatches] at hshape
      | cons field fields ih =>
          cases values with
          | nil =>
              simp [panValueShape, panShapeMatches,
                panShapeMatches.panShapeListMatches] at hshape
          | cons value values =>
              simp only [List.map_cons, panValueShape, panShapeMatches,
                panShapeMatches.panShapeListMatches, Bool.and_eq_true] at hshape
              obtain ⟨fieldWord, hfieldWord⟩ := panValueShape_matches_one_inv
                structs field hshape.1
              have htailShape :
                  panShapeMatches (panValueShape structs (.rStruct fields))
                    (.comb (values.map (fun _ => .one))) = true := by
                simpa [panValueShape, panShapeMatches] using hshape.2
              obtain ⟨tailValues, htailValue, htailLength⟩ := ih
                (values := values) htailShape
              refine ⟨fieldWord :: tailValues, ?_, ?_⟩
              · cases hfieldWord
                have hfields : fields =
                    tailValues.map (fun value => .word value) := by
                  injection htailValue
                simp [hfields]
              · simp [htailLength]

end Flapjack
