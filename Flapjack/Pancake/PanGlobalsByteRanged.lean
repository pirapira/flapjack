import Flapjack.Pancake.PanGlobals
import Flapjack.Parser.ByteRanged

/-!
Generated-name byte-rangedness witnesses for the `pan_globals` pass
(bead `flapjack-0up.3`).

The production fresh-name algorithms append apostrophes (`'`, code 39) to an
input name until it is absent from a list of names:

* `freshNameHOL` is the source-shaped port of HOL `fresh_name_def`
  (`pan_globalsScript.sml:55`) and is what the executed entry-point renaming
  `globalNewMainName` uses (`Flapjack/Pipeline.lean:612`);
* `globalFreshName`/`globalFreshNameAux` are the fuel-bounded production
  counterparts (same result, `names.length` fuel).

This module proves that both algorithms preserve `StringByteRanged`, i.e. the
identifier carrier used at the exact `mlstring` boundary never gains a byte
`>= 256`.  `StringByteRanged` is the parser-chain predicate
(`Flapjack/Parser/ByteRanged.lean`), definitionally equal to the
`NameRanged` predicate used by `DeclByteRanged`/`ProgByteRanged`
(`Flapjack/Pancake/PanLang/Prog.lean:21`).

Nothing here is tagged: these are supporting byte-boundary witnesses for the
future `names_as_string`-qualified `PanGlobals` retag
(`docs/PANGLOBALS-CARRIER-REVIEW.md`).
-/

namespace Flapjack

open Flapjack.Parser

/-- Concatenation preserves byte-rangedness. -/
theorem stringByteRanged_append {s₁ s₂ : String}
    (h₁ : StringByteRanged s₁) (h₂ : StringByteRanged s₂) :
    StringByteRanged (s₁ ++ s₂) := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with h | h
  · exact h₁ c h
  · exact h₂ c h

/-- The apostrophe appended by the fresh-name search is a single byte. -/
theorem stringByteRanged_quote : StringByteRanged "'" := by
  unfold StringByteRanged CharsByteRanged
  decide

/-- `globalApostrophes` only ever produces apostrophes. -/
theorem globalApostrophes_byteRanged (count : Nat) :
    StringByteRanged (globalApostrophes count) := by
  induction count with
  | zero => simp [globalApostrophes, StringByteRanged, CharsByteRanged]
  | succ count ih =>
      rw [globalApostrophes]
      exact stringByteRanged_append stringByteRanged_quote ih

/-- The fuel-bounded production fresh-name search preserves byte-rangedness. -/
theorem globalFreshNameAux_byteRanged [BEq String] (name : String)
    (h : StringByteRanged name) (names : List String) (candidate fuel : Nat) :
    StringByteRanged (globalFreshNameAux name names candidate fuel) := by
  induction fuel generalizing candidate with
  | zero =>
      rw [globalFreshNameAux]
      exact stringByteRanged_append h (globalApostrophes_byteRanged candidate)
  | succ fuel ih =>
      rw [globalFreshNameAux]
      by_cases hc : names.contains (name ++ globalApostrophes candidate) = true
      · rw [if_pos hc]
        exact ih (candidate + 1)
      · rw [if_neg hc]
        exact stringByteRanged_append h (globalApostrophes_byteRanged candidate)

/-- Production `globalFreshName` preserves byte-rangedness. -/
theorem globalFreshName_byteRanged [BEq String] (name : String)
    (h : StringByteRanged name) (names : List String) :
    StringByteRanged (globalFreshName name names) :=
  globalFreshNameAux_byteRanged name h names 0 names.length

/-- The source-shaped HOL `fresh_name` port preserves byte-rangedness. -/
theorem freshNameHOL_byteRanged (name : String) (names : List String)
    (h : StringByteRanged name) :
    StringByteRanged (freshNameHOL name names) := by
  fun_induction freshNameHOL name names with
  | case1 name names ih =>
      exact ih (stringByteRanged_append h stringByteRanged_quote)
  | case2 name names => exact h

/-- The executed entry-point name `new_main_name` stays byte-ranged. -/
theorem globalNewMainName_byteRanged (declarations : List (Decl α)) :
    StringByteRanged (globalNewMainName declarations) := by
  unfold globalNewMainName
  exact freshNameHOL_byteRanged "main" (globalFunctionNames declarations)
    (by unfold StringByteRanged CharsByteRanged; decide)

end Flapjack
