import Flapjack.Parser.ByteRanged
import Flapjack.Parser.ConversionByteRanged

/-! Kernel checks for the byte-rangedness foundation (bead
    `flapjack-pxn.18.3.5.8.7.1`).  These are the reusable lemmas the parser
    invariant proof builds on. -/

namespace Flapjack.Test.ParserByteRangedParity

open Flapjack.Parser
open Flapjack.Basis.Pure.MlString

example (s : String) : CharsByteRanged (utf8Bytes s) := utf8Bytes_byteRanged s

example (s : String) : StringByteRanged (String.ofList (utf8Bytes s)) :=
  stringByteRanged_ofList (utf8Bytes_byteRanged s)

example (b : UInt8) : (Char.ofNat b.toNat).toNat = b.toNat := char_ofNat_uint8 b

example : (readWhile isAlphaNumOrWild ['a', 'b', '1', '_'] []).1 = "ab1_" := by decide

example : CharsByteRanged (readWhile isAlphaNumOrWild ['a', 'b', '1', '_'] []).1.toList :=
  readWhile_charsByteRanged isAlphaNumOrWild_impliesByte _ [] (by simp [CharsByteRanged])

example : (readWhile isDigitAscii ['1', '2', 'x'] []).1 = "12" := by decide

example (l : List Char) (h : CharsByteRanged l) (n : Nat) : CharsByteRanged (l.drop n) :=
  charsByteRanged_drop h n

example (l : List Char) (h : CharsByteRanged l) (n : Nat) : CharsByteRanged (l.take n) :=
  charsByteRanged_take h n

example (c : Char) (cs : List Char) (h : CharsByteRanged (c :: cs)) : CharsByteRanged cs :=
  charsByteRanged_tail h

example (s : String) (h : StringByteRanged s) :
    StringByteRanged (String.ofList (s.toList.drop 1)) :=
  drop_one_stringByteRanged h

example (s : String) (h : CharsByteRanged s.toList) :
    CharsByteRanged (readWhile isAlphaNumOrWild s.toList []).1.toList :=
  readWhile_charsByteRanged' s.toList [] h (by simp [CharsByteRanged])

example (s : String) (h : StringByteRanged s) : TokenNameByteRanged (getKeyword s) :=
  getKeyword_nameByteRanged s h

example (s : String) : TokenNameByteRanged (getToken s) :=
  getToken_nameByteRanged s

example (a : Atom) (h : AtomNameByteRanged a) : TokenNameByteRanged (tokenOfAtom a) :=
  tokenOfAtom_nameByteRanged h

example : getToken "&&" = Token.boolAndT := by decide

example : getKeyword "skip" = Token.keywordT Keyword.skipK := by decide

example : getKeyword "abc" = Token.identT "abc" := by decide

example : getKeyword "@ffi" = Token.foreignIdent "ffi" := by decide

example (input : String) (p : Token × Locs) (hp : p ∈ pancakeLex input) :
    TokenNameByteRanged p.1 :=
  pancakeLex_tokens_byteRanged input p hp

example (fuel : Nat) (input : List Char) (loc : Posn) (h : CharsByteRanged input)
    (p : Token × Locs) (hp : p ∈ lexAux fuel input loc) : TokenNameByteRanged p.1 :=
  lexAux_tokens_byteRanged fuel input loc h p hp

/-! Direct parity with the original-HOL `get_keyword` oracle
    (`scripts/hol-probes/pan_lexer_get_keyword_probe.out`,
    bead `flapjack-pxn.18.3.5.8.7.2`): every table entry and fallback. -/

example : getKeyword "st" = Token.keywordT Keyword.stK := by decide
example : getKeyword "stw" = Token.keywordT Keyword.stwK := by decide
example : getKeyword "st8" = Token.keywordT Keyword.st8K := by decide
example : getKeyword "st16" = Token.keywordT Keyword.st16K := by decide
example : getKeyword "st32" = Token.keywordT Keyword.st32K := by decide
example : getKeyword "if" = Token.keywordT Keyword.ifK := by decide
example : getKeyword "else" = Token.keywordT Keyword.elseK := by decide
example : getKeyword "while" = Token.keywordT Keyword.whileK := by decide
example : getKeyword "break" = Token.keywordT Keyword.brK := by decide
example : getKeyword "continue" = Token.keywordT Keyword.contK := by decide
example : getKeyword "throw" = Token.keywordT Keyword.throwK := by decide
example : getKeyword "return" = Token.keywordT Keyword.retK := by decide
example : getKeyword "tick" = Token.keywordT Keyword.ticK := by decide
example : getKeyword "var" = Token.keywordT Keyword.varK := by decide
example : getKeyword "in" = Token.keywordT Keyword.inK := by decide
example : getKeyword "try" = Token.keywordT Keyword.tryK := by decide
example : getKeyword "catch" = Token.keywordT Keyword.catchK := by decide
example : getKeyword "lds" = Token.keywordT Keyword.ldsK := by decide
example : getKeyword "ldw" = Token.keywordT Keyword.ldwK := by decide
example : getKeyword "ld8" = Token.keywordT Keyword.ld8K := by decide
example : getKeyword "ld16" = Token.keywordT Keyword.ld16K := by decide
example : getKeyword "ld32" = Token.keywordT Keyword.ld32K := by decide
example : getKeyword "@base" = Token.keywordT Keyword.baseK := by decide
example : getKeyword "@top" = Token.keywordT Keyword.baseK := by decide
example : getKeyword "@biw" = Token.keywordT Keyword.biwK := by decide
example : getKeyword "true" = Token.keywordT Keyword.trueK := by decide
example : getKeyword "false" = Token.keywordT Keyword.falseK := by decide
example : getKeyword "fun" = Token.keywordT Keyword.funK := by decide
example : getKeyword "export" = Token.keywordT Keyword.exportK := by decide
example : getKeyword "inline" = Token.keywordT Keyword.inlineK := by decide
example : getKeyword "exception" = Token.keywordT Keyword.exceptionK := by decide
example : getKeyword "struct" = Token.keywordT Keyword.namedK := by decide
example : getKeyword "" = Token.lexErrorT "Expected keyword, found empty string" := by
  decide
example : getKeyword "@" = Token.identT "@" := by decide

example (name : String) (h : StringByteRanged name) : StringByteRanged name :=
  convIdent_byteRanged (parseTreeByteRanged_lf (token := .identT name) (locs := unknownLoc) h) rfl

example (name : String) (h : StringByteRanged name) : StringByteRanged name :=
  convFfiIdent_byteRanged (parseTreeByteRanged_lf (token := .foreignIdent name)
    (locs := unknownLoc) h) rfl

end Flapjack.Test.ParserByteRangedParity
