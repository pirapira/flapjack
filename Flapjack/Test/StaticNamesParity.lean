import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `static_check_names_def`
    (`cakeml/pancake/panStaticScript.sml:1945-1980`). -/

def staticNamesCheck (declarations : List (Decl Nat)) :
    StaticResult StructContext :=
  staticCheckNames ([] : StructContext) declarations

#guard
  staticResultErrorMessage
      (staticNamesCheck
        [.name "Pair" [("left", .one)],
          .name "Pair" [("right", .one)]]) ==
    some "struct name Pair is redeclared in top-level declaration\n"

#guard
  staticResultErrorMessage
      (staticNamesCheck
        [.name "Pair" [("z", .one), ("a", .one), ("a", .one)]]) ==
    some "field a is redeclared in struct name Pair\n"

#guard
  staticResultErrorMessage
      (staticNamesCheck [.name "Pair" [("missing", .named "Missing")]]) ==
    some "struct name Missing is not in scope in declaration of field missing in named struct Pair\n"

#guard
  match (staticNamesCheck
      [.name "Pair" [("left", .one), ("right", .one)],
        .function
          { name := "ignored"
            inline := false
            exported := false
            params := []
            body := .skip
            returnShape := .one }]).1 with
  | Except.ok structs =>
      match lookupInfo "Pair" structs with
      | some info =>
          info.fields.map (fun (name, shape) => (name, Shape.shapeToString shape)) ==
              [("left", "1"), ("right", "1")] && info.size == 2
      | none => false
  | Except.error _ => false

end Flapjack
