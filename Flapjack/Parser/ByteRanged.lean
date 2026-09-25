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

/-- `readWhile` leaves a suffix of its input, hence a byte-ranged remainder. -/
theorem readWhile_rest_charsByteRanged {p : Char → Bool} (input acc : List Char)
    (hinput : CharsByteRanged input) : CharsByteRanged (readWhile p input acc).2 := by
  induction input generalizing acc with
  | nil => intro c hc; simp [readWhile] at hc
  | cons c cs ih =>
      by_cases h : p c
      · simp only [readWhile, h]
        exact ih (c :: acc) (charsByteRanged_tail hinput)
      · simp only [readWhile, h]
        exact hinput

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

theorem charsByteRanged_tail' {l : List Char} (h : CharsByteRanged l) :
    CharsByteRanged l.tail := by
  cases l with
  | nil => intro c hc; simp at hc
  | cons c cs => exact charsByteRanged_tail h

set_option maxHeartbeats 2000000 in
/-- Byte-rangedness is preserved by `nextAtom`: the returned atom carries no
    non-byte name and the remaining input is byte-ranged. -/
theorem nextAtom_byteRanged : ∀ fuel input loc, CharsByteRanged input →
    ∀ a locs rest, nextAtom fuel input loc = some (a, locs, rest) →
    AtomNameByteRanged a ∧ CharsByteRanged rest := by
  intro fuel
  induction fuel with
  | zero => intro input loc _ a locs rest h; simp [nextAtom] at h
  | succ fuel ih =>
    intro input loc hinput a locs rest h
    cases input with
    | nil => simp [nextAtom] at h
    | cons c cs =>
      have hcs : CharsByteRanged cs := charsByteRanged_tail hinput
      have hc : c.toNat < 256 := hinput c (by simp)
      have hrst : ∀ (p : Char → Bool) (acc : List Char),
          CharsByteRanged (readWhile p cs acc).2 :=
        fun p acc => readWhile_rest_charsByteRanged cs acc hcs
      simp only [nextAtom] at h
      by_cases h1 : (c == '\n') = true
      · rw [if_pos h1] at h; exact ih cs (nextLine loc) hcs a locs rest h
      · rw [if_neg h1] at h
        by_cases h2 : isSpaceAscii c = true
        · rw [if_pos h2] at h; exact ih cs (nextLoc 1 loc) hcs a locs rest h
        · rw [if_neg h2] at h
          by_cases h3 : isDigitAscii c = true
          · rw [if_pos h3] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, rfl⟩ := h
            exact ⟨trivial, hrst isDigitAscii [c]⟩
          · rw [if_neg h3] at h
            by_cases h4 : (c == '-' && (Option.map isDigitAscii cs.head?).getD false) = true
            · rw [if_pos h4] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -, rfl⟩ := h
              exact ⟨trivial, hrst isDigitAscii []⟩
            · rw [if_neg h4] at h
              by_cases h5 : (c == '/' && cs.head? == some '/') = true
              · rw [if_pos h5] at h
                split at h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, -, rfl⟩ := h
                  exact ⟨trivial, by simp [CharsByteRanged]⟩
                · exact ih (cs.drop _) _ (charsByteRanged_drop hcs _) a locs rest h
              · rw [if_neg h5] at h
                by_cases h6 : (c == '/' && cs.head? == some '@') = true
                · rw [if_pos h6] at h
                  split at h
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, -, rfl⟩ := h
                    exact ⟨trivial, by simp [CharsByteRanged]⟩
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, -, rfl⟩ := h
                    exact ⟨trivial, charsByteRanged_drop hcs _⟩
                · rw [if_neg h6] at h
                  by_cases h7 : (c == '/' && cs.head? == some '*') = true
                  · rw [if_pos h7] at h
                    split at h
                    · simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, -, rfl⟩ := h
                      exact ⟨trivial, by simp [CharsByteRanged]⟩
                    · exact ih (cs.drop _) _ (charsByteRanged_drop hcs _) a locs rest h
                  · rw [if_neg h7] at h
                    by_cases h8 : isAtomSingleton c = true
                    · rw [if_pos h8] at h
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, -, rfl⟩ := h
                      exact ⟨trivial, hcs⟩
                    · rw [if_neg h8] at h
                      by_cases h9 : isAtomBeginGroup c = true
                      · rw [if_pos h9] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, -, rfl⟩ := h
                        exact ⟨trivial, hrst isAtomInGroup [c]⟩
                      · rw [if_neg h9] at h
                        by_cases h10 : (isAlphaAscii c || c == '@' || c == '_') = true
                        · rw [if_pos h10] at h
                          simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, -, rfl⟩ := h
                          exact ⟨readWhile_charsByteRanged' cs [c] hcs (charsByteRanged_singleton hc),
                            hrst isAlphaNumOrWild [c]⟩
                        · rw [if_neg h10] at h
                          simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, -, rfl⟩ := h
                          exact ⟨trivial, hcs⟩

/-- Byte-rangedness is preserved by `nextToken`. -/
theorem nextToken_byteRanged {fuel : Nat} {input : List Char} {loc : Posn}
    (hinput : CharsByteRanged input) :
    ∀ token locs rest, nextToken fuel input loc = some (token, locs, rest) →
    TokenNameByteRanged token ∧ CharsByteRanged rest := by
  intro token locs rest h
  unfold nextToken at h
  split at h
  · simp at h
  · rename_i atom locs' rest' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    obtain ⟨ha, hrest⟩ := nextAtom_byteRanged fuel input loc hinput atom locs' rest' heq
    exact ⟨tokenOfAtom_nameByteRanged ha, hrest⟩

/-- Every token produced by `lexAux` from a byte-ranged input has a byte-ranged
    name (all other tokens are name-free). -/
theorem lexAux_tokens_byteRanged : ∀ fuel input loc, CharsByteRanged input →
    ∀ p ∈ lexAux fuel input loc, TokenNameByteRanged p.1 := by
  intro fuel
  induction fuel with
  | zero => intro input loc _ p hp; simp [lexAux] at hp
  | succ fuel ih =>
    intro input loc hinput p hp
    cases input with
    | nil => simp [lexAux, nextToken, nextAtom] at hp
    | cons c cs =>
      simp only [lexAux] at hp
      split at hp
      · simp at hp
      · rename_i token locs rest heq
        rw [List.mem_cons] at hp
        rcases hp with hhead | htail
        · subst hhead
          exact (nextToken_byteRanged hinput token locs rest heq).1
        · exact ih rest locs.stop (nextToken_byteRanged hinput token locs rest heq).2 p htail

/-- The executable lexer only ever emits byte-ranged identifier names. -/
theorem pancakeLex_tokens_byteRanged (input : String) :
    ∀ p ∈ pancakeLex input, TokenNameByteRanged p.1 := by
  intro p hp
  unfold pancakeLex at hp
  exact lexAux_tokens_byteRanged ((utf8Bytes input).length + 1) (utf8Bytes input) initLoc
    (utf8Bytes_byteRanged input) p hp

end Flapjack.Parser
