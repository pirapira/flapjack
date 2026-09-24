import Flapjack.Pancake.WordLang

/-!
# Exact width-indexed `word_loc` parity

Kernel and `#guard` checks that `WordLocW 8` matches the HOL `word_loc`
oracle (`scripts/hol-probes/word_lang_word_loc_probe.out`: `Word 7w`,
`Loc 3 4`, constructors distinct) and that the untagged bridge to the generic
`WordLoc (BitVec width)` round-trips.
-/

namespace Flapjack.Test.WordLocWParity

open Flapjack

private abbrev W := BitVec 8

/-- HOL `wl_word = Word 7w`. -/
example : (WordLocW.word (BitVec.ofNat 8 7) : WordLocW 8) =
    WordLocW.word (BitVec.ofNat 8 7) := rfl

/-- HOL `wl_loc = Loc 3 4`. -/
example : (WordLocW.loc 3 4 : WordLocW 8) = WordLocW.loc 3 4 := rfl

/-- HOL `wl_distinct = F`: the two constructors are distinct. -/
example : (WordLocW.word (BitVec.ofNat 8 0) : WordLocW 8) ≠ WordLocW.loc 0 0 := by decide

/-- The generic bridge maps `Word` payloads unchanged. -/
example : wordLocWToGeneric (WordLocW.word (BitVec.ofNat 8 7) : WordLocW 8) =
    (WordLoc.word (BitVec.ofNat 8 7) : WordLoc (BitVec 8)) := rfl

/-- The generic bridge maps `Loc` payloads unchanged. -/
example : wordLocWToGeneric (WordLocW.loc 3 4 : WordLocW 8) =
    (WordLoc.loc 3 4 : WordLoc (BitVec 8)) := rfl

/-- Round trip `WordLocW -> WordLoc -> WordLocW`. -/
example (location : WordLocW 8) : wordLocWOfGeneric (wordLocWToGeneric location) = location :=
  wordLocWOfGeneric_toGeneric location

/-- Round trip `WordLoc -> WordLocW -> WordLoc`. -/
example (location : WordLoc (BitVec 8)) :
    wordLocWToGeneric (wordLocWOfGeneric location) = location :=
  wordLocWToGeneric_ofGeneric location

/-- Executable mirror of the four oracle rows. -/
private def wordLocGuard : Bool :=
  (WordLocW.word (BitVec.ofNat 8 7) == (WordLocW.word (BitVec.ofNat 8 7) : WordLocW 8)) &&
    (WordLocW.loc 3 4 == (WordLocW.loc 3 4 : WordLocW 8)) &&
    ((WordLocW.word (BitVec.ofNat 8 0) : WordLocW 8) != WordLocW.loc 0 0) &&
    ((match (WordLocW.loc 3 4 : WordLocW 8) with
      | .word _ => 1
      | .loc _ _ => 2) == 2)

#guard wordLocGuard

def runChecks : IO Bool := do
  if wordLocGuard then
    IO.println "PASS wordLang word_loc exact width-indexed carrier matches all 4 oracle rows"
  else
    IO.println "FAIL wordLang word_loc exact width-indexed carrier"
  pure wordLocGuard

end Flapjack.Test.WordLocWParity