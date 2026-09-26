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

/-! ## Production bridge for the exact `shape_to_str` port

FLAPJACK-SPECIFIC (no `@[hol]` tag). HOL `panLang$shape_to_str`
(`cakeml/pancake/panLangScript.sml:180-188`) is ported exactly as the tagged
`shapeToStrHOL` over `ShapeHOL`/`MlS`.  The executed diagnostics
(`Flapjack.Pancake.PanStatic` and friends) instead use the production
`Flapjack.Shape.shapeToString`, whose name carrier is `String`.  The theorem
`ofString_shapeToString` connects the two at the `mlstring` level through the
`shapeToHOL` codec; under `ShapeByteRanged` the `String` identity follows by
`toStringOfBytes_ofString_of_bytes`. -/

private theorem ofString_empty :
    Flapjack.Basis.Pure.MlString.ofString ("" : String) = (Flapjack.Basis.Pure.MlString.MlString.implode []) := by
  simp only [Flapjack.Basis.Pure.MlString.ofString]
  rfl

private theorem mlstrAppend_implode_nil_left (x : MlS) :
    mlstrAppend (Flapjack.Basis.Pure.MlString.MlString.implode []) x = x := by
  simp only [mlstrAppend, Flapjack.Basis.Pure.MlString.MlString.explode_implode,
    Flapjack.Basis.Pure.MlString.MlString.implode_explode, List.nil_append]

private theorem mlstrAppend_ofString_empty (x : MlS) :
    mlstrAppend (Flapjack.Basis.Pure.MlString.ofString "") x = x := by
  rw [ofString_empty]
  exact mlstrAppend_implode_nil_left x

private theorem mlstrAppend_implode_nil (x : MlS) :
    mlstrAppend x (.implode []) = x := by
  simp only [mlstrAppend, Flapjack.Basis.Pure.MlString.MlString.explode_implode,
    Flapjack.Basis.Pure.MlString.MlString.implode_explode, List.append_nil]

theorem ofString_append (left right : String) :
    Flapjack.Basis.Pure.MlString.ofString (left ++ right) =
      mlstrAppend (Flapjack.Basis.Pure.MlString.ofString left)
        (Flapjack.Basis.Pure.MlString.ofString right) := by
  simp only [Flapjack.Basis.Pure.MlString.ofString, mlstrAppend,
    Flapjack.Basis.Pure.MlString.MlString.explode_implode, String.toList_append,
    List.map_append]

theorem mlstrAppend_assoc (a b c : MlS) :
    mlstrAppend (mlstrAppend a b) c = mlstrAppend a (mlstrAppend b c) := by
  simp only [mlstrAppend, Flapjack.Basis.Pure.MlString.MlString.explode_implode,
    List.append_assoc]

theorem mlstrConcat_append (left right : List MlS) :
    mlstrConcat (left ++ right) =
      mlstrAppend (mlstrConcat left) (mlstrConcat right) := by
  induction left with
  | nil => simp only [List.nil_append, mlstrConcat, mlstrAppend_implode_nil_left]
  | cons part rest ih =>
      simp only [List.cons_append, mlstrConcat, ih, mlstrAppend_assoc]

theorem shapeToStrHOL_shapeToHOL_comb_cons (head : Flapjack.Shape)
    (tail : List Flapjack.Shape) :
    shapeToStrHOL (shapeToHOL (Shape.comb (head :: tail))) =
      mlstrConcat
        (Flapjack.Basis.Pure.MlString.ofString "{" ::
          shapeToStrHOL (shapeToHOL head) ::
          (tail.map (fun field =>
            mlstrAppend (Flapjack.Basis.Pure.MlString.ofString ",")
              (shapeToStrHOL (shapeToHOL field)))) ++
          [Flapjack.Basis.Pure.MlString.ofString "}"]) := by
  simp only [shapeToHOL, List.map_cons, shapeToStrHOL, List.map_map]
  rfl

private theorem ofString_fold (fields : List Flapjack.Shape) :
    ∀ (init : String)
      (_ih : ∀ field ∈ fields,
        Flapjack.Basis.Pure.MlString.ofString (Shape.shapeToString field) =
          shapeToStrHOL (shapeToHOL field)),
    Flapjack.Basis.Pure.MlString.ofString
        (fields.foldl (fun result field => result ++ "," ++ Shape.shapeToString field) init) =
      mlstrAppend (Flapjack.Basis.Pure.MlString.ofString init)
        (mlstrConcat (fields.map (fun field =>
          mlstrAppend (Flapjack.Basis.Pure.MlString.ofString ",")
            (shapeToStrHOL (shapeToHOL field))))) := by
  induction fields with
  | nil => intro init _; simp [mlstrConcat, mlstrAppend_implode_nil]
  | cons field rest ihRest =>
      intro init ih
      rw [List.foldl_cons,
        ihRest (init ++ "," ++ Shape.shapeToString field)
          (fun member hmember => ih member (by simp [hmember]))]
      rw [ofString_append, ofString_append, ih field (by simp)]
      simp only [List.map_cons, mlstrConcat, mlstrAppend_assoc]

/-- Production bridge: `ofString (Shape.shapeToString s)` is the exact
    `shapeToStrHOL (shapeToHOL s)`.  FLAPJACK-SPECIFIC, untagged (production
    diagnostics versus the tagged HOL counterpart). -/
theorem ofString_shapeToString (s : Flapjack.Shape) :
    Flapjack.Basis.Pure.MlString.ofString (Shape.shapeToString s) =
      shapeToStrHOL (shapeToHOL s) := by
  induction s using Flapjack.Shape.shapeToString.induct with
  | case1 => simp only [Shape.shapeToString, shapeToHOL, shapeToStrHOL]
  | case2 => simp only [Shape.shapeToString, shapeToHOL, List.map_nil, shapeToStrHOL]
  | case3 head tail ihHead ihTail =>
      rw [shapeToStrHOL_shapeToHOL_comb_cons, Shape.shapeToString]
      rw [ofString_append, ofString_append, ofString_append]
      rw [ihHead, ofString_fold tail "" (fun field hf => ihTail field hf)]
      simp only [mlstrAppend_ofString_empty]
      simp only [List.cons_append, mlstrConcat, mlstrConcat_append,
        mlstrAppend_implode_nil, mlstrAppend_assoc]
  | case4 name => simp only [Shape.shapeToString, shapeToHOL, shapeToStrHOL]

private theorem string_append_bytes {a b : String}
    (ha : ∀ c ∈ a.toList, c.toNat < 256) (hb : ∀ c ∈ b.toList, c.toNat < 256) :
    ∀ c ∈ (a ++ b).toList, c.toNat < 256 := by
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with h | h
  · exact ha c h
  · exact hb c h

private theorem foldl_bytes (fields : List Flapjack.Shape) :
    ∀ (init : String), (∀ c ∈ init.toList, c.toNat < 256) →
      (∀ field ∈ fields, ∀ c ∈ (Shape.shapeToString field).toList, c.toNat < 256) →
      ∀ c ∈ (fields.foldl (fun result field => result ++ "," ++ Shape.shapeToString field) init).toList,
        c.toNat < 256 := by
  induction fields with
  | nil => intro init hinit _; simpa using hinit
  | cons field rest ih =>
      intro init hinit hfields
      simp only [List.foldl_cons]
      apply ih
      · apply string_append_bytes
        · apply string_append_bytes hinit
          exact (by decide : ∀ c ∈ ("," : String).toList, c.toNat < 256)
        · exact hfields field (by simp)
      · intro f hf; exact hfields f (by simp [hf])

/-- Every character of a byte-ranged shape's production rendering is a byte.
    `Shape.shapeToString` concatenates literal separators and the recursive
    renderings, so the only source of characters is the `named` case, where
    `ShapeByteRanged` supplies the bound.  FLAPJACK-SPECIFIC, untagged. -/
theorem shapeByteRanged_shapeToString_bytes (s : Flapjack.Shape) :
    ShapeByteRanged s → ∀ c ∈ (Shape.shapeToString s).toList, c.toNat < 256 := by
  induction s using Flapjack.Shape.shapeToString.induct with
  | case1 => intro _; simp only [Shape.shapeToString]; decide
  | case2 => intro _; simp only [Shape.shapeToString]; decide
  | case3 head tail ihHead ihTail =>
      intro h
      simp only [ShapeByteRanged] at h
      have hhead : ∀ c ∈ (Shape.shapeToString head).toList, c.toNat < 256 :=
        ihHead (h head (by simp))
      have htail : ∀ f ∈ tail, ∀ c ∈ (Shape.shapeToString f).toList, c.toNat < 256 :=
        fun f hf => ihTail f hf (h f (by simp [hf]))
      intro c hc
      rw [Shape.shapeToString] at hc
      have hfold := foldl_bytes tail "" (by decide) htail
      repeat rw [String.toList_append, List.mem_append] at hc
      rcases hc with hc | hD
      · rcases hc with hc | hC
        · rcases hc with hA | hB
          · exact (by decide : ∀ c ∈ ("{" : String).toList, c.toNat < 256) c hA
          · exact hhead c hB
        · exact hfold c hC
      · exact (by decide : ∀ c ∈ ("}" : String).toList, c.toNat < 256) c hD
  | case4 name => intro h; simpa only [ShapeByteRanged, Shape.shapeToString] using h

/-- String-level corollary of `ofString_shapeToString`: when every character of
    the production rendering is a byte, `toStringOfBytes` inverts `ofString` and
    recovers `Shape.shapeToString`.  FLAPJACK-SPECIFIC, untagged. -/
theorem shapeToString_eq_shapeToStrHOL_toStringOfBytes (s : Flapjack.Shape)
    (h : ∀ c ∈ (Shape.shapeToString s).toList, c.toNat < 256) :
    Shape.shapeToString s =
      Flapjack.Basis.Pure.MlString.toStringOfBytes (shapeToStrHOL (shapeToHOL s)) := by
  rw [← ofString_shapeToString s,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes]
  exact h

/-- Premise-free form of the production bridge: `ShapeByteRanged` already
    guarantees the byte premise, so this closes the `.1.28` diagnostic-string
    bridge without an extra hypothesis.  FLAPJACK-SPECIFIC, untagged. -/
theorem shapeToString_eq_shapeToStrHOL_toStringOfBytes_of_byteRanged (s : Flapjack.Shape)
    (h : ShapeByteRanged s) :
    Shape.shapeToString s =
      Flapjack.Basis.Pure.MlString.toStringOfBytes (shapeToStrHOL (shapeToHOL s)) :=
  shapeToString_eq_shapeToStrHOL_toStringOfBytes s (shapeByteRanged_shapeToString_bytes s h)

end Flapjack.Pancake.PanLang
