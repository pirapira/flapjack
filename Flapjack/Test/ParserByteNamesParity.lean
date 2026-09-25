import Flapjack.Parser

/-!
Direct oracle parity for the byte-faithful PanLexer (bead
`flapjack-pxn.18.3.5.8.7`).

The rows reproduce `scripts/hol-probes/pan_lexer_bytes_probe.out`, the direct
`EVAL` output of the original `panLexerScript.sml` on byte-valued inputs. HOL
`char` has exactly 256 values and `string` is a `char list`, and
`isAlphaNum` is the ASCII range test from `stringScript.sml:74-95`, so a byte
>= 128 is neither a letter nor a digit and `pancake_lex` reports a lexical
error instead of an identifier.

Source bytes are modelled with `Flapjack.Parser.utf8Bytes`: a Lean `String`
holding the codepoint 206 encodes back to the two UTF-8 bytes `0xC3 0x8E`, so
the lexer observes the same bytes CakeML would read from the file.
-/

namespace Flapjack.Test.ParserByteNamesParity

open Flapjack.Parser

/-- A byte-valued character, as the original lexer sees it. -/
private def byte (n : Nat) : Char := Char.ofNat n

private def firstTokenIsError (s : String) : Bool :=
  match (pancakeLex s).head? with
  | some (token, _) => match token with
    | .lexErrorT _ => true
    | _ => false
  | none => false

private def firstIdentLength (s : String) : Nat :=
  match (pancakeLex s).head? with
  | some (.identT name, _) => name.length
  | _ => 0

/-- `plx_alpha_206`: `isAlphaNum (CHR 206) = F`. -/
private def alpha206Row : Bool := isAlphaNumAscii (byte 206) == false
/-- `plx_alpha_ascii`: `isAlphaNum #"a" = T`. -/
private def alphaAsciiRow : Bool := isAlphaNumAscii (byte 97) == true
/-- `plx_alpha_accent`: `isAlphaNum (CHR 233) = F`. -/
private def alphaAccentRow : Bool := isAlphaNumAscii (byte 233) == false
/-- `plx_high_first_iserror`: `pancake_lex [CHR 206; #"x"]` starts with `LexErrorT`. -/
private def highFirstIsErrorRow : Bool :=
  firstTokenIsError (String.ofList [byte 206, byte 120]) == true
/-- `plx_ascii_ident_len`: `pancake_lex [#"a"; #"b"; #"c"]` gives `IdentT "abc"`. -/
private def asciiIdentLenRow : Bool := firstIdentLength "abc" == 3
/-- `plx_ascii_then_high`: `pancake_lex [#"a"; #"b"; CHR 206]` gives `IdentT "ab"` then a `LexErrorT`. -/
private def asciiThenHighRow : Bool :=
  firstIdentLength (String.ofList [byte 97, byte 98, byte 206]) == 2

def parityGuard : Bool :=
  alpha206Row && alphaAsciiRow && alphaAccentRow &&
    highFirstIsErrorRow && asciiIdentLenRow && asciiThenHighRow

#eval parityGuard
#guard parityGuard

/-- Kernel-checked: every character the (byte-faithful) lexer admits into an
identifier is a byte below 128, so a parsed name never contains a byte >= 128
and `MlString.ofString` cannot truncate it. -/
example (c : Char) (h : isAlphaNumOrWild c = true) : c.toNat < 128 :=
  isAlphaNumOrWild_lt128 h

end Flapjack.Test.ParserByteNamesParity
