import Flapjack.HolRef

/-!
# Faithful Cake `mlstring` carrier

Lean counterpart of `cakeml/basis/pure/mlstringScript.sml`:

```
Datatype:
  mlstring = implode string
End
```

HOL `string` is `char list`, and HOL `char` is the canonical 256-element type
(`HOL/src/string/stringScript.sml` defines it through the bijection
`CHR : num -> char`, `ORD : char -> num`).  `HolChar` models HOL `char` by
`BitVec 8`, the canonical 256-element carrier, exactly as HOL `word` types are
modeled by `BitVec width` throughout Flapjack.  The single constructor `implode`
of `MlString` is then exactly HOL's `mlstring = implode string`, so the datatype
is shape-exact and carries no word-width or typeclass side condition.

This is the carrier needed to make the `stackLang`/`stack_names` program
theorems exact, since HOL `stackLang$prog` is polymorphic in a single word type
and its FFI constructor stores an `mlstring`, whereas the executable
`Flapjack.Compiler.Backend.StackCarrier.ProgW` uses Lean `String`.
-/

namespace Flapjack.Basis.Pure.MlString

/-- Model of HOL `char`: the canonical 256-element type.  HOL `char` is an
abstract type with a bijection `CHR`/`ORD` to the 256 values; `BitVec 8` has the
same cardinality and exposes the same data, matching the repo convention of
modeling HOL word types with `BitVec`. -/
abbrev HolChar := BitVec 8

/-- Exact port of HOL `Datatype: mlstring = implode string`
    (`cakeml/basis/pure/mlstringScript.sml:19-21`).

    `string` is `char list`; with `HolChar = BitVec 8` the field is
    `List (BitVec 8)`.  Single-constructor datatype with no side condition. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring"]
inductive MlString where
  | implode (data : List HolChar)
  deriving Repr, DecidableEq

namespace MlString

/-- HOL `explode`: the underlying character list.  Structural accessor matching
    `mlstringScript.sml:70-72` (`explode s = explode_aux s 0 (strlen s)`, with
    `explode (strlit ls) = ls`).  Untagged infrastructure. -/
def explode : MlString → List HolChar
  | .implode data => data

@[simp] theorem explode_implode (data : List HolChar) :
    explode (.implode data) = data := rfl

/-- HOL `implode_explode` (`mlstringScript.sml:86-90`). -/
@[simp] theorem implode_explode (s : MlString) : MlString.implode (explode s) = s := by
  cases s
  rfl

end MlString



/-- Kernel-checked byte codec between the executable Lean `String` and the
faithful HOL `mlstring = implode string`.

HOL `strlit` of a `char list` corresponds to `MlString.implode` of the same
character codes; the executable Flapjack `stackLang`/`stack_names` program
carrier stores FFI names as Lean `String`.  `ofString` encodes a Lean string by
the low byte of each character code (`BitVec.ofNat 8` truncates modulo 256,
exactly HOL `ORD`/`CHR` on 8-bit characters) and `toStringOfBytes` decodes the
bytes back.  Both are Flapjack-specific infrastructure (no single HOL
counterpart), so they stay untagged.

`toStringOfBytes_ofString_of_bytes` recovers a Lean string exactly when every
character code is < 256, i.e. on the byte range HOL `char` can represent;
`ofString_toStringOfBytes` is total on `MlString`.  These give the checked
relationship needed to relate a production `String` FFI field to the exact
`mlstring` carrier (bead `flapjack-pxn.18.5.15.3.11.2.3`). -/
def ofString (s : String) : MlString :=
  .implode (s.toList.map (fun c => BitVec.ofNat 8 c.toNat))

/-- Decode an `MlString` to a Lean `String` by reading each byte as a character
code.  See `ofString`. -/
def toStringOfBytes (m : MlString) : String :=
  String.ofList (m.explode.map (fun b => Char.ofNat b.toNat))

@[simp] theorem explode_ofString (s : String) :
    (ofString s).explode = s.toList.map (fun c => BitVec.ofNat 8 c.toNat) := rfl

/-- `Char.ofNat` preserves byte-ranged codes. -/
theorem ofNat_toNat_char (b : BitVec 8) : (Char.ofNat b.toNat).toNat = b.toNat := by
  have hvalid : b.toNat.isValidChar := by
    simp only [Nat.isValidChar]
    left
    have := b.isLt
    omega
  rw [Char.ofNat, dif_pos hvalid]
  unfold Char.ofNatAux
  simp

/-- Encoding a byte-ranged character code is exact. -/
theorem char_of_byte_toNat (c : Char) (h : c.toNat < 256) :
    (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by
  rw [BitVec.toNat_ofNat]
  change c.toNat % 256 = c.toNat
  exact Nat.mod_eq_of_lt h

/-- `MlString -> String -> MlString` round trips exactly. -/
theorem ofString_toStringOfBytes (m : MlString) :
    ofString (toStringOfBytes m) = m := by
  cases m with
  | implode data =>
    unfold toStringOfBytes ofString
    simp only [MlString.explode_implode, String.toList_ofList, List.map_map]
    congr 1
    simpa only [List.map_id] using
      List.map_congr_left (l := data) (g := id)
        (fun b _ => by
          rw [Function.comp_apply, ofNat_toNat_char, id_eq]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat]
          change b.toNat % 256 = b.toNat
          exact Nat.mod_eq_of_lt (by have := b.isLt; simpa using this))

/-- `String -> MlString -> String` recovers the original string exactly when
every character code is < 256 (the range HOL `char` represents). -/
theorem toStringOfBytes_ofString_of_bytes (s : String)
    (h : ∀ c ∈ s.toList, c.toNat < 256) :
    toStringOfBytes (ofString s) = s := by
  apply String.toList_inj.mp
  unfold toStringOfBytes ofString
  rw [String.toList_ofList, MlString.explode_implode, List.map_map]
  simpa only [List.map_id] using
    List.map_congr_left (l := s.toList) (g := id)
      (fun c hc => by
        rw [Function.comp_apply, char_of_byte_toNat c (h c hc)]
        simp [Char.ofNat_toNat])

end Flapjack.Basis.Pure.MlString
