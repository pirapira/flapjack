import Flapjack.Parser.Lexer
import Flapjack.Basis.Pure.MlString

/-!
Byte-rangedness foundation for the Pancake parser (bead
`flapjack-pxn.18.3.5.8.7.1`).

HOL `string` is a `char list` with exactly 256 values, so a CakeML parser can
never produce a name containing a codepoint `>= 256`.  The executable Lean
lexer reads the source as `utf8Bytes`, so every character it sees already
satisfies that bound; this module proves the two basic facts the parser-level
proof needs:

* `utf8Bytes` produces only characters with `toNat < 256`, and
* `readWhile` over a predicate that implies the bound produces only
  byte-ranged strings.

The remaining step -- lifting this through `nextAtom`/`lexAux` to a token
stream invariant and then through the grammar and `convTopDecList` to
`Parser.parseTopDecs` -- is tracked as a child bead of
`flapjack-pxn.18.3.5.8.7.1`.  None of this is tagged: the parser is
Flapjack-specific production infrastructure.
-/

open Flapjack.Basis.Pure.MlString

namespace Flapjack.Parser

/-- A character list every character of which is a HOL byte (`toNat < 256`). -/
def CharsByteRanged (l : List Char) : Prop := ∀ c ∈ l, c.toNat < 256

/-- A string every character of which is a HOL byte (`toNat < 256`). -/
def StringByteRanged (s : String) : Prop := CharsByteRanged s.toList

theorem stringByteRanged_ofList {l : List Char} (h : CharsByteRanged l) :
    StringByteRanged (String.ofList l) := by
  simpa [StringByteRanged, CharsByteRanged] using h

/-- `Char.ofNat` of a `UInt8` codepoint is that same codepoint. -/
theorem char_ofNat_uint8 (b : UInt8) : (Char.ofNat b.toNat).toNat = b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  have h := ofNat_toNat_char (BitVec.ofNat 8 b.toNat)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at h

/-- The UTF-8 encoding of any string consists only of bytes. -/
theorem utf8Bytes_byteRanged (s : String) : CharsByteRanged (utf8Bytes s) := by
  intro c hc
  simp only [utf8Bytes, List.mem_map] at hc
  obtain ⟨b, _, rfl⟩ := hc
  rw [char_ofNat_uint8]
  exact b.toNat_lt

/-- A character predicate that implies the byte bound. -/
def ImpliesByte (p : Char → Bool) : Prop := ∀ c, p c = true → c.toNat < 256

theorem isAlphaNumOrWild_impliesByte : ImpliesByte isAlphaNumOrWild :=
  fun _ h => Nat.lt_of_lt_of_le (isAlphaNumOrWild_lt128 h) (by omega)

theorem isDigitAscii_impliesByte : ImpliesByte isDigitAscii :=
  fun _ h => Nat.lt_of_lt_of_le (isDigitAscii_lt128 h) (by omega)

theorem charsByteRanged_singleton {c : Char} (h : c.toNat < 256) :
    CharsByteRanged [c] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  exact h

theorem charsByteRanged_reverse {l : List Char} (h : CharsByteRanged l) :
    CharsByteRanged l.reverse := by
  intro c hc
  exact h c (by simpa using hc)

/-- `readWhile` preserves byte-rangedness of the accepted prefix. -/
theorem readWhile_charsByteRanged {p : Char → Bool} (hp : ImpliesByte p)
    (input acc : List Char) (hacc : CharsByteRanged acc) :
    CharsByteRanged (readWhile p input acc).1.toList := by
  induction input generalizing acc with
  | nil => simpa [readWhile] using charsByteRanged_reverse hacc
  | cons c cs ih =>
      by_cases h : p c
      · simp only [readWhile, h]
        refine ih (c :: acc) ?_
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hp _ h
        · exact hacc d hd
      · simp only [readWhile, h]
        simpa using charsByteRanged_reverse hacc

theorem charsByteRanged_tail {c : Char} {cs : List Char} (h : CharsByteRanged (c :: cs)) :
    CharsByteRanged cs := by
  intro d hd
  exact h d (by simp [hd])

theorem charsByteRanged_drop {l : List Char} (h : CharsByteRanged l) (n : Nat) :
    CharsByteRanged (l.drop n) := by
  intro c hc
  exact h c (by simpa using List.mem_of_mem_drop hc)

theorem charsByteRanged_take {l : List Char} (h : CharsByteRanged l) (n : Nat) :
    CharsByteRanged (l.take n) := by
  intro c hc
  exact h c (by simpa using List.mem_of_mem_take hc)

/-- Unconditional form: `readWhile` accepts only characters from `input` or `acc`. -/
theorem readWhile_charsByteRanged' {p : Char → Bool} (input acc : List Char)
    (hinput : CharsByteRanged input) (hacc : CharsByteRanged acc) :
    CharsByteRanged (readWhile p input acc).1.toList := by
  induction input generalizing acc with
  | nil => simpa [readWhile] using charsByteRanged_reverse hacc
  | cons c cs ih =>
      have hcs : CharsByteRanged cs := charsByteRanged_tail hinput
      have hc : c.toNat < 256 := hinput c (by simp)
      by_cases h : p c
      · simp only [readWhile, h]
        exact ih (c :: acc) hcs (fun d hd => by
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hc
          · exact hacc d hd)
      · simp only [readWhile, h]
        simpa using charsByteRanged_reverse hacc

/-- Name-carrying payloads of a lexer atom are byte-ranged. -/
def AtomNameByteRanged : Atom → Prop
  | .wordA text => StringByteRanged text
  | _ => True

/-- Name-carrying payloads of a lexer token are byte-ranged. -/
def TokenNameByteRanged : Token → Prop
  | .identT name => StringByteRanged name
  | .foreignIdent name => StringByteRanged name
  | _ => True

theorem drop_one_stringByteRanged {s : String} (h : StringByteRanged s) :
    StringByteRanged (String.ofList (s.toList.drop 1)) :=
  stringByteRanged_ofList (charsByteRanged_drop h 1)

/-- A value found by the ordered token-table lookup is an entry of that table. -/
theorem lookupTable_mem {α : Type} {t : List (String × α)} {s : String} {v : α}
    (h : lookupTable t s = some v) : (s, v) ∈ t := by
  induction t with
  | nil => simp [lookupTable] at h
  | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      simp only [lookupTable] at h
      by_cases hc : s == key
      · rw [if_pos hc] at h
        have hs : s = key := by simpa using hc
        have hv : value = v := by simpa using h
        subst hs; subst hv; simp
      · rw [if_neg hc] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Every token in the symbolic table carries no identifier name. -/
theorem symbolTable_ok : ∀ p ∈ symbolTable, TokenNameByteRanged p.2 := by
  simp [symbolTable, TokenNameByteRanged]

/-- `getToken` never returns a name-carrying token. -/
theorem getToken_nameByteRanged (s : String) : TokenNameByteRanged (getToken s) := by
  unfold getToken
  split
  · rename_i token heq
    exact symbolTable_ok (s, token) (lookupTable_mem heq)
  · exact trivial

/-- A byte-ranged string yields a byte-ranged `getKeyword` result: keyword and
    error tokens carry no name, while the fallback is `s` or `drop 1 s`. -/
theorem getKeyword_nameByteRanged (s : String) (h : StringByteRanged s) :
    TokenNameByteRanged (getKeyword s) := by
  unfold getKeyword
  split
  · rename_i k heq
    exact trivial
  · by_cases hz : s == ""
    · rw [if_pos hz]; exact trivial
    · rw [if_neg hz]
      by_cases hf : (2 ≤ s.length && s.front == '@') = true
      · rw [if_pos hf]; exact drop_one_stringByteRanged h
      · rw [if_neg hf]; exact h

/-- Byte-rangedness is preserved by atom-to-token conversion. -/
theorem tokenOfAtom_nameByteRanged {a : Atom} (h : AtomNameByteRanged a) :
    TokenNameByteRanged (tokenOfAtom a) := by
  cases a with
  | numberA value => exact trivial
  | wordA text => exact getKeyword_nameByteRanged text h
  | symA text => exact getToken_nameByteRanged text
  | errA message => exact trivial
  | annotCommentA text => exact trivial

end Flapjack.Parser
