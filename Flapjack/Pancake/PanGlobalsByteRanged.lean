import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
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

/-! ## `NameRanged` witness API

The declarations below expose the byte-boundary facts under the `NameRanged`
name used by `DeclByteRanged`/`ProgByteRanged` (`NameRanged` is definitionally
`StringByteRanged`).  They are the same-module checked witnesses that the
`names_as_string` qualifier tooling (`flapjack-an4`) consumes; every generated
name carries an explicit `NameRanged` input premise, and the executed parser
boundary `parseTopDecs_declByteRanged` discharges those premises. -/

/-- Witness: `freshNameHOL` preserves `NameRanged` under an explicit premise. -/
theorem freshNameHOL_nameRanged (name : String) (names : List String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) :=
  freshNameHOL_byteRanged name names h

/-- Witness: `globalFreshNameAux` preserves `NameRanged` under an explicit premise. -/
theorem globalFreshNameAux_nameRanged [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String)
    (candidate fuel : Nat) :
    Flapjack.Pancake.PanLang.NameRanged
      (globalFreshNameAux name names candidate fuel) :=
  globalFreshNameAux_byteRanged name h names candidate fuel

/-- Witness: production `globalFreshName` preserves `NameRanged`. -/
theorem globalFreshName_nameRanged [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String) :
    Flapjack.Pancake.PanLang.NameRanged (globalFreshName name names) :=
  globalFreshName_byteRanged name h names

/-- Witness: the executed entry-point name `new_main_name` is `NameRanged`
    (the literal `"main"` needs no premise). -/
theorem globalNewMainName_nameRanged (declarations : List (Decl α)) :
    Flapjack.Pancake.PanLang.NameRanged (globalNewMainName declarations) :=
  globalNewMainName_byteRanged declarations

/-- Extraction: a byte-ranged production `ExtCall` program has a byte-ranged
    FFI function name.  This is the precondition the production FFI boundary
    witness (`flapjack-0up.2`) consumes. -/
theorem progByteRanged_extCall_name {width : Nat} {function : String}
    {configuration configurationLength array arrayLength : Flapjack.Exp (BitVec width)}
    (h : Flapjack.Pancake.PanLang.ProgByteRanged
      (Flapjack.Prog.extCall function configuration configurationLength array arrayLength :
        Flapjack.Prog (BitVec width))) :
    Flapjack.Pancake.PanLang.NameRanged function :=
  h.1

/-- Extraction: a byte-ranged function declaration has a byte-ranged name. -/
theorem declByteRanged_function_name {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : Flapjack.Pancake.PanLang.DeclByteRanged (Flapjack.Decl.function fd)) :
    Flapjack.Pancake.PanLang.NameRanged fd.name :=
  h.1

/-- Extraction: a byte-ranged function declaration body has a byte-ranged name. -/
theorem funDeclByteRanged_name {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : Flapjack.Pancake.PanLang.FunDeclByteRanged fd) :
    Flapjack.Pancake.PanLang.NameRanged fd.name :=
  h.1

end Flapjack
