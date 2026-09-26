import Flapjack.Pancake.PanLang
import Flapjack.Basis.Pure.MlString

/-!
# Exact `panLang$shape` over the faithful `mlstring` carrier

HOL `panLang$shape` (`cakeml/pancake/panLangScript.sml:35-39`) is

```
shape = One | Comb (shape list) | Named stcname
```

where `stcname = mlstring` (lines 23-24) and
`mlstring = implode string` (`cakeml/basis/pure/mlstringScript.sml:19-21`).

The executable `Flapjack.Shape` in `Flapjack/Pancake/PanLang.lean` types the
`named` field by Lean `String`, so its `@[hol ... "shape"]` tag is not exact (a
`String` is a sequence of Unicode characters, whereas HOL `mlstring` is a list
of 8-bit characters).  `ShapeHOL` below is the exact counterpart: the same
constructor arities `0/1/1` with `comb : List ShapeHOL` and
`named : MlString`.

`shapeToHOL`/`shapeOfHOL` are the kernel-checked codec between production
`Flapjack.Shape` and `ShapeHOL`.  Encoding `String -> mlstring` is total
(`ofString`, low-byte truncation, exactly HOL `ORD`/`CHR` on bytes) and
`shapeToHOL_shapeOfHOL` round trips `ShapeHOL` exactly.  The reverse direction
`shapeOfHOL_shapeToHOL` recovers a production shape exactly on byte-ranged names
(`ShapeByteRanged`), the range HOL `char` represents; outside that range the
production `String` name is not representable as an `mlstring`, which is why
production syntax cannot itself be tagged as the exact HOL datatype.

Direct HOL oracle rows for the `named` field as an `mlstring` are recorded in
`scripts/hol-probes/pan_lang_shape_probe.out` and reproduced by
`Flapjack/Test/PanLangShapeHOLParity.lean`.
-/

namespace Flapjack.Pancake.PanLang

/-- The faithful Cake `mlstring` carrier, local abbreviation. -/
abbrev MlS := Flapjack.Basis.Pure.MlString.MlString

/-- Exact port of HOL `panLang$shape` (`cakeml/pancake/panLangScript.sml:35-39`).

    The `named` field is a `stcname`, which HOL aliases to `mlstring`
    (lines 23-24); `MlS` is the faithful carrier.  Constructor arities
    `0/1/1` and field types `List ShapeHOL` and `MlS` match the HOL datatype,
    so this is the exact `shape` declaration.  Like production `Flapjack.Shape`
    it derives only `Repr` (a `DecidableEq` instance is not needed and the HOL
    equality is the datatype equality). -/
@[hol "cakeml/pancake/panLangScript.sml" "shape"]
inductive ShapeHOL where
  | one
  | comb (fields : List ShapeHOL)
  | named (name : MlS)
  deriving Repr

/-- Production shapes whose every `named` name is byte-ranged: each character
    code of every name is `< 256`, the range HOL `char` represents.  Such a
    `Flapjack.Shape` is exactly representable as an `mlstring`-named shape. -/
def ShapeByteRanged : Flapjack.Shape → Prop
  | .one => True
  | .comb fields => ∀ field ∈ fields, ShapeByteRanged field
  | .named name => ∀ c ∈ name.toList, c.toNat < 256

/-- Encode a production `Flapjack.Shape` into the exact HOL-shaped carrier.
    Names are encoded by the total `MlString.ofString` (per-character low
    byte), matching HOL `ORD`/`CHR` on the byte range. -/
def shapeToHOL : Flapjack.Shape → ShapeHOL
  | .one => .one
  | .comb fields => .comb (fields.map shapeToHOL)
  | .named name => .named (Flapjack.Basis.Pure.MlString.ofString name)

/-- Decode the exact carrier back to a production `Flapjack.Shape`.  Names are
    decoded by `MlString.toStringOfBytes`, reading each byte as a character
    code. -/
def shapeOfHOL : ShapeHOL → Flapjack.Shape
  | .one => .one
  | .comb fields => .comb (fields.map shapeOfHOL)
  | .named name => .named (Flapjack.Basis.Pure.MlString.toStringOfBytes name)

/-- `ShapeHOL -> Shape -> ShapeHOL` round trips exactly: every `MlString` is
    byte-valued, so `ofString` inverts `toStringOfBytes`. -/
@[simp] theorem shapeToHOL_shapeOfHOL : (h : ShapeHOL) →
    shapeToHOL (shapeOfHOL h) = h
  | .one => by simp [shapeOfHOL, shapeToHOL]
  | .comb fields => by
    simp only [shapeOfHOL, shapeToHOL, List.map_map]
    congr 1
    have hmap : List.map (shapeToHOL ∘ shapeOfHOL) fields = List.map id fields :=
      List.map_congr_left (fun field _ => shapeToHOL_shapeOfHOL field)
    rw [hmap, List.map_id]
  | .named name => by
    simp [shapeOfHOL, shapeToHOL,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]

/-- `Shape -> ShapeHOL -> Shape` round trips exactly on byte-ranged shapes. -/
@[simp] theorem shapeOfHOL_shapeToHOL : (s : Flapjack.Shape) → ShapeByteRanged s →
    shapeOfHOL (shapeToHOL s) = s
  | .one, _ => by simp [shapeOfHOL, shapeToHOL]
  | .comb fields, h => by
    simp only [ShapeByteRanged] at h
    simp only [shapeOfHOL, shapeToHOL, List.map_map]
    congr 1
    have hmap : List.map (shapeOfHOL ∘ shapeToHOL) fields = List.map id fields :=
      List.map_congr_left (fun field hfield =>
        shapeOfHOL_shapeToHOL field (h field hfield))
    rw [hmap, List.map_id]
  | .named name, hbytes => by
    simp only [ShapeByteRanged] at hbytes
    simp [shapeOfHOL, shapeToHOL,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hbytes]

/-! HOL `panLang$size_of_shape` (`cakeml/pancake/panLangScript.sml:174-177`):
    `One -> 1`, `Comb shapes -> SUM (MAP size_of_shape shapes)`, and
    `Named name -> 1` (the HOL comment notes the named case "should not happen").
    This is the context-free counterpart of `size_of_sh_with_ctxt`; it never
    inspects the structure context, so it lives over the exact `ShapeHOL`
    carrier. -/
mutual
  @[hol "cakeml/pancake/panLangScript.sml" "size_of_shape_def"]
  def sizeOfShapeHOL : ShapeHOL → Nat
    | .one => 1
    | .comb shapes => sizeOfShapesHOL shapes
    | .named _ => 1
  def sizeOfShapesHOL : List ShapeHOL → Nat
    | [] => 0
    | shape :: shapes => sizeOfShapeHOL shape + sizeOfShapesHOL shapes
end

@[simp] theorem sizeOfShapeHOL_one : sizeOfShapeHOL (.one : ShapeHOL) = 1 := by
  simp only [sizeOfShapeHOL]

@[simp] theorem sizeOfShapeHOL_comb (shapes : List ShapeHOL) :
    sizeOfShapeHOL (.comb shapes) = sizeOfShapesHOL shapes := by
  simp only [sizeOfShapeHOL]

@[simp] theorem sizeOfShapeHOL_named (name : MlS) :
    sizeOfShapeHOL (.named name) = 1 := by
  simp only [sizeOfShapeHOL]

@[simp] theorem sizeOfShapesHOL_nil : sizeOfShapesHOL ([] : List ShapeHOL) = 0 := by
  simp only [sizeOfShapesHOL]

@[simp] theorem sizeOfShapesHOL_cons (shape : ShapeHOL) (shapes : List ShapeHOL) :
    sizeOfShapesHOL (shape :: shapes) =
      sizeOfShapeHOL shape + sizeOfShapesHOL shapes := by
  simp only [sizeOfShapesHOL]

/-! HOL `panLang$shape_to_str` (`cakeml/pancake/panLangScript.sml:180-188`)
    turns a shape into its `mlstring` rendering with `strlit` literals and `^`
    (mlstring concatenation).  The production `Flapjack.Shape.shapeToString`
    cannot be tagged because its carrier is a Lean `String`; the exact port over
    `ShapeHOL` returns the faithful `MlS` carrier and uses the two untagged
    `mlstring` helpers below. -/

/-- HOL `mlstring$^` (concatenation): append the two underlying character
    lists.  Untagged infrastructure (HOL `mlstringScript.sml` is outside the
    CakeML submodule). -/
def mlstrAppend (left right : MlS) : MlS :=
  .implode (left.explode ++ right.explode)

/-- HOL `concat` on an `mlstring list`: fold the list with `^`, left to right. -/
def mlstrConcat : List MlS → MlS
  | [] => .implode []
  | part :: parts => mlstrAppend part (mlstrConcat parts)

/-- Exact port of HOL `panLang$shape_to_str_def`
    (`cakeml/pancake/panLangScript.sml:180-188`) over the faithful `ShapeHOL`
    and `MlS` carriers: `One -> strlit "1"`; `Comb [] -> strlit "{}"` (HOL
    comments it "should never happen"); `Comb (x::xs)` is the `concat` of
    `strlit "{"`, `shape_to_str x`, the `"," ^ _` renders of `xs`, and
    `strlit "}"`; `Named nm -> nm`.  `strlit` is `MlString.ofString` (exact on
    the ASCII literals used here). -/
@[hol "cakeml/pancake/panLangScript.sml" "shape_to_str_def"]
def shapeToStrHOL : ShapeHOL → MlS
  | .one => Flapjack.Basis.Pure.MlString.ofString "1"
  | .comb [] => Flapjack.Basis.Pure.MlString.ofString "{}"
  | .comb (head :: tail) =>
      mlstrConcat
        (Flapjack.Basis.Pure.MlString.ofString "{" ::
          shapeToStrHOL head ::
          (tail.map (fun field =>
            mlstrAppend (Flapjack.Basis.Pure.MlString.ofString ",")
              (shapeToStrHOL field))) ++
          [Flapjack.Basis.Pure.MlString.ofString "}"])
  | .named name => name

private theorem ofString_append (left right : String) :
    Flapjack.Basis.Pure.MlString.ofString (left ++ right) =
      mlstrAppend (Flapjack.Basis.Pure.MlString.ofString left)
        (Flapjack.Basis.Pure.MlString.ofString right) := by
  simp [Flapjack.Basis.Pure.MlString.ofString, mlstrAppend,
    Flapjack.Basis.Pure.MlString.MlString.explode_implode,
    String.toList_append, List.map_append]

private theorem mlstrAppend_assoc (first second third : MlS) :
    mlstrAppend (mlstrAppend first second) third =
      mlstrAppend first (mlstrAppend second third) := by
  simp [mlstrAppend, Flapjack.Basis.Pure.MlString.MlString.explode_implode,
    List.append_assoc]

private theorem mlstrConcat_append (left right : List MlS) :
    mlstrConcat (left ++ right) =
      mlstrAppend (mlstrConcat left) (mlstrConcat right) := by
  induction left with
  | nil => simp [mlstrConcat, mlstrAppend]
  | cons head tail ih =>
      simp only [List.cons_append, mlstrConcat]
      rw [ih, mlstrAppend_assoc]

private theorem foldlShapeStrings_append_prefix (fields : List Flapjack.Shape)
    (leading initial : String) :
    fields.foldl
        (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
        (leading ++ initial) =
      leading ++ fields.foldl
        (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
        initial := by
  induction fields generalizing leading initial with
  | nil => simp
  | cons field fields ih =>
      simp only [List.foldl_cons]
      simpa only [String.append_assoc] using
        ih leading (initial ++ "," ++ Flapjack.Shape.shapeToString field)

private theorem shapeToStringTail_toHOL (tail : List Flapjack.Shape)
    (h : ∀ field ∈ tail,
      Flapjack.Basis.Pure.MlString.ofString (Flapjack.Shape.shapeToString field) =
        shapeToStrHOL (shapeToHOL field)) :
    Flapjack.Basis.Pure.MlString.ofString
        (tail.foldl
          (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field) "") =
      mlstrConcat (tail.map (fun field =>
        mlstrAppend (Flapjack.Basis.Pure.MlString.ofString ",")
          (shapeToStrHOL (shapeToHOL field)))) := by
  induction tail with
  | nil => simp [mlstrConcat, Flapjack.Basis.Pure.MlString.ofString]
  | cons field tail ih =>
      have hfield := h field (by simp)
      have htail : ∀ nested ∈ tail,
          Flapjack.Basis.Pure.MlString.ofString
              (Flapjack.Shape.shapeToString nested) =
            shapeToStrHOL (shapeToHOL nested) := by
        intro nested hmem
        exact h nested (by simp [hmem])
      have ihTail := ih htail
      rw [List.foldl_cons]
      have hfold := foldlShapeStrings_append_prefix tail
        ("," ++ Flapjack.Shape.shapeToString field) ""
      have hfold' :
          tail.foldl
              (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
              ("," ++ Flapjack.Shape.shapeToString field) =
            ("," ++ Flapjack.Shape.shapeToString field) ++
              tail.foldl
                (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
                "" := by
        simpa using hfold
      rw [show "" ++ "," ++ Flapjack.Shape.shapeToString field =
          "," ++ Flapjack.Shape.shapeToString field by simp]
      rw [hfold']
      rw [ofString_append, ofString_append, hfield, ihTail]
      simp [mlstrConcat, mlstrAppend_assoc]

private theorem shapeToString_toHOL (shape : Flapjack.Shape) :
    Flapjack.Basis.Pure.MlString.ofString (Flapjack.Shape.shapeToString shape) =
      shapeToStrHOL (shapeToHOL shape) := by
  fun_induction Flapjack.Shape.shapeToString shape with
  | case1 => simp [shapeToStrHOL, shapeToHOL]
  | case2 => simp [shapeToStrHOL, shapeToHOL]
  | case3 head tail ihHead ihTail =>
    have htail := shapeToStringTail_toHOL tail ihTail
    simp_all [shapeToHOL, shapeToStrHOL, mlstrAppend, mlstrConcat, List.map_map,
      Flapjack.Basis.Pure.MlString.ofString,
      Flapjack.Basis.Pure.MlString.MlString.explode_implode,
      String.toList_append, List.map_append, mlstrConcat_append]
    have hHeadBytes := congrArg Flapjack.Basis.Pure.MlString.MlString.explode ihHead
    have hTailBytes := congrArg Flapjack.Basis.Pure.MlString.MlString.explode htail
    simp only [Flapjack.Basis.Pure.MlString.MlString.explode] at hHeadBytes hTailBytes
    simp only [Flapjack.Basis.Pure.MlString.MlString.explode]
    rw [hHeadBytes]
    exact congrArg
      (fun bytes : List Flapjack.Basis.Pure.MlString.HolChar =>
        (shapeToStrHOL (shapeToHOL head)).explode ++ (bytes ++ [125#8])) hTailBytes
  | case4 name => simp [shapeToStrHOL, shapeToHOL]

private def StringByteRanged (text : String) : Prop :=
  ∀ character ∈ text.toList, character.toNat < 256

private theorem stringSingletonByteRanged (character : Char)
    (hcharacter : character.toNat < 256) :
  StringByteRanged (String.singleton character) := by
  intro other hother
  simp only [String.singleton, String.toList_push, String.toList_empty,
    List.mem_append, List.mem_singleton] at hother
  rcases hother with hnil | heq
  · cases hnil
  · subst other
    exact hcharacter

private theorem stringByteRanged_append {left right : String}
    (hleft : StringByteRanged left) (hright : StringByteRanged right) :
    StringByteRanged (left ++ right) := by
  intro character hcharacter
  simp only [String.toList_append, List.mem_append] at hcharacter
  rcases hcharacter with hleft' | hright'
  · exact hleft character hleft'
  · exact hright character hright'

private theorem shapeToStringTail_byteRanged (tail : List Flapjack.Shape)
    (h : ∀ field ∈ tail,
      StringByteRanged (Flapjack.Shape.shapeToString field)) :
    StringByteRanged
      (tail.foldl
        (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field) "") := by
  induction tail with
  | nil =>
      intro character hcharacter
      change character ∈ ([] : List Char) at hcharacter
      cases hcharacter
  | cons field tail ih =>
      have hfield := h field (by simp)
      have htail : ∀ nested ∈ tail,
          StringByteRanged (Flapjack.Shape.shapeToString nested) := by
        intro nested hmem
        exact h nested (by simp [hmem])
      have ihTail := ih htail
      have hcomma : StringByteRanged "," := by
        simpa using stringSingletonByteRanged ',' (by decide)
      have hfirst := stringByteRanged_append hcomma hfield
      have hfold := foldlShapeStrings_append_prefix tail
        ("," ++ Flapjack.Shape.shapeToString field) ""
      have hfold' :
          tail.foldl
              (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
              ("," ++ Flapjack.Shape.shapeToString field) =
            ("," ++ Flapjack.Shape.shapeToString field) ++
              tail.foldl
                (fun result field => result ++ "," ++ Flapjack.Shape.shapeToString field)
                "" := by
        simpa using hfold
      simp only [List.foldl_cons]
      rw [show "" ++ "," ++ Flapjack.Shape.shapeToString field =
          "," ++ Flapjack.Shape.shapeToString field by simp, hfold']
      exact stringByteRanged_append hfirst ihTail

private theorem shapeToString_byteRanged (shape : Flapjack.Shape)
    (hshape : ShapeByteRanged shape) :
    StringByteRanged (Flapjack.Shape.shapeToString shape) := by
  revert hshape
  fun_induction Flapjack.Shape.shapeToString shape with
  | case1 =>
      intro _
      simpa [Flapjack.Shape.shapeToString] using
        stringSingletonByteRanged '1' (by decide)
  | case2 =>
      intro _
      have hopen : StringByteRanged (String.singleton '{') :=
        stringSingletonByteRanged '{' (by decide)
      have hclose : StringByteRanged (String.singleton '}') :=
        stringSingletonByteRanged '}' (by decide)
      simpa [Flapjack.Shape.shapeToString] using stringByteRanged_append hopen hclose
  | case3 head tail ihHead ihTail =>
      intro hshape
      simp only [ShapeByteRanged] at hshape
      have hhead := ihHead (hshape head (by simp))
      have htail : ∀ field ∈ tail,
          StringByteRanged (Flapjack.Shape.shapeToString field) := by
        intro field hmem
        exact ihTail field hmem (hshape field (by simp [hmem]))
      have hfold := shapeToStringTail_byteRanged tail htail
      have hopen : StringByteRanged ("{" ++ Flapjack.Shape.shapeToString head) := by
        apply stringByteRanged_append
        · simpa using stringSingletonByteRanged '{' (by decide)
        · exact hhead
      have hclosed := stringByteRanged_append hopen hfold
      have hbrace : StringByteRanged "}" := by
        simpa using stringSingletonByteRanged '}' (by decide)
      simpa [Flapjack.Shape.shapeToString] using
        stringByteRanged_append hclosed hbrace
  | case4 name =>
      intro hname
      simpa [StringByteRanged, ShapeByteRanged,
        Flapjack.Shape.shapeToString] using hname

/-- Production diagnostic rendering agrees with the exact HOL
    `shape_to_str_def` on byte-ranged shapes. The premise is needed because
    `String -> MlString` truncates non-byte characters; `shapeToStrHOL` itself
    remains the tagged definition over the exact MlString carrier. This bridge
    is untagged infrastructure connecting the executable String implementation
    to that port; it has no separate HOL declaration because it relates the
    Flapjack String/MlString codec to the tagged definition. -/
theorem shapeToString_eq_shapeToStrHOL_toStringOfBytes
    (shape : Flapjack.Shape) (hshape : ShapeByteRanged shape) :
    Flapjack.Shape.shapeToString shape =
      Flapjack.Basis.Pure.MlString.toStringOfBytes
        (shapeToStrHOL (shapeToHOL shape)) := by
  calc
    Flapjack.Shape.shapeToString shape =
        Flapjack.Basis.Pure.MlString.toStringOfBytes
          (Flapjack.Basis.Pure.MlString.ofString
            (Flapjack.Shape.shapeToString shape)) := by
      symm
      exact Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        _ (shapeToString_byteRanged shape hshape)
    _ = Flapjack.Basis.Pure.MlString.toStringOfBytes
          (shapeToStrHOL (shapeToHOL shape)) := by
      rw [shapeToString_toHOL]

/-! HOL `panLang$with_shape` (`cakeml/pancake/panLangScript.sml:216-220`) splits
    a list into consecutive blocks whose lengths are the `size_of_shape` of each
    shape: `with_shape [] _ = []` and `with_shape (sh::shs) e = TAKE
    (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e)`.  The
    exact port is polymorphic in the list element type and uses the tagged
    `sizeOfShapeHOL`; `TAKE`/`DROP` are Lean's `List.take`/`List.drop`. -/
@[hol "cakeml/pancake/panLangScript.sml" "with_shape_def"]
def withShapeHOL {α : Type} : List ShapeHOL → List α → List (List α)
  | [], _ => []
  | shape :: shapes, values =>
      values.take (sizeOfShapeHOL shape) ::
        withShapeHOL shapes (values.drop (sizeOfShapeHOL shape))

end Flapjack.Pancake.PanLang
