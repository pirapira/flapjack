import Flapjack.Parser.ByteRanged

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

end Flapjack.Test.ParserByteRangedParity