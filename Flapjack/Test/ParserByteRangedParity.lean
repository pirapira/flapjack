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

end Flapjack.Test.ParserByteRangedParity