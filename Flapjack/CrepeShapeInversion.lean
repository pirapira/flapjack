import Flapjack.PanValues

/-!
Shape inversion for flattened word records.  A Crep shape that matches the
shape emitted for a scalar word-record value must be the corresponding
`Shape.comb` of one-word fields.  This exposes the invariant needed to connect
the source local's recorded shape with the assignment destination shape.
-/

namespace Flapjack

theorem panShapeMatches_word_record_shape_inv
    [BEq String] [LawfulBEq String]
    (values : List α) (shape : Shape)
    (hshape : panShapeMatches
      (.comb (values.map (fun _ => .one))) shape = true) :
    shape = .comb (values.map (fun _ => .one)) := by
  induction values generalizing shape with
  | nil =>
      cases shape with
      | one => simp [panShapeMatches] at hshape
      | named name => simp [panShapeMatches] at hshape
      | comb shapes =>
          cases shapes with
          | nil => rfl
          | cons head tail =>
              simp [panShapeMatches, panShapeMatches.panShapeListMatches] at hshape
  | cons value values ih =>
      cases shape with
      | one => simp [panShapeMatches] at hshape
      | named name => simp [panShapeMatches] at hshape
      | comb shapes =>
          cases shapes with
          | nil => simp [panShapeMatches,
              panShapeMatches.panShapeListMatches] at hshape
          | cons head tail =>
              have hhead : head = .one := by
                cases head with
                | one => rfl
                | named name =>
                    simp [panShapeMatches,
                      panShapeMatches.panShapeListMatches] at hshape
                | comb shapes =>
                    simp [panShapeMatches,
                      panShapeMatches.panShapeListMatches] at hshape
              have htailShape : panShapeMatches
                  (.comb (values.map (fun _ => .one))) (.comb tail) = true := by
                simpa [panShapeMatches,
                  panShapeMatches.panShapeListMatches, hhead] using hshape
              have htailComb := ih (.comb tail) htailShape
              have htail : tail = values.map (fun _ => .one) := by
                injection htailComb
              simp [hhead, htail]

end Flapjack
