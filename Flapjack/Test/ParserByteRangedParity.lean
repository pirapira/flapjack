import Flapjack.Parser.ByteRanged
import Flapjack.Parser.ConversionByteRanged

/-! Kernel checks for the byte-rangedness foundation (bead
    `flapjack-pxn.18.3.5.8.7.1`).  These are the reusable lemmas the parser
    invariant proof builds on. -/

namespace Flapjack.Test.ParserByteRangedParity

open Flapjack.Parser
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

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

example (fuel : Nat) :
    Flapjack.Pancake.PanLang.ShapeByteRanged Flapjack.Shape.one :=
  convShape_byteRanged (fuel + 1)
    (ParseTree.lf Token.defaultShT unknownLoc)
    (parseTreeByteRanged_lf (token := Token.defaultShT) (locs := unknownLoc)
      (by simp [TokenNameByteRanged]))
    Flapjack.Shape.one (by simp [convShape, convDefaultShape, ParseTree.destTok])

example (fuel : Nat) : convParams fuel [] = some [] := rfl

example (fuel : Nat) (p : VarName × Shape)
    (hp : p ∈ ([] : List (VarName × Shape))) :
    StringByteRanged p.1 ∧ ShapeByteRanged p.2 :=
  convParams_byteRanged fuel [] (by simp) [] rfl p hp

example (fuel : Nat) (result : String × List (VarName × Shape))
    (h : convStructName fuel (ParseTree.lf Token.semiT unknownLoc) = some result) :
    StringByteRanged result.1 ∧
      ∀ p ∈ result.2, StringByteRanged p.1 ∧ ShapeByteRanged p.2 :=
  convStructName_byteRanged
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc)
      (by simp [TokenNameByteRanged])) result h


example {tree : ParseTree} (ht : ParseTreeByteRanged tree)
    (e : Flapjack.Exp (BitVec 64)) (h : convVar (α := BitVec 64) tree = some e) :
    ExpByteRanged e :=
  convVar_byteRanged ht e h

example (ofInt : Int → BitVec 64) {tree : ParseTree}
    (e : Flapjack.Exp (BitVec 64)) (h : convConst ofInt tree = some e) :
    ExpByteRanged e :=
  convConst_byteRanged ofInt e h

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (acc : Flapjack.Exp (BitVec 64)) (hacc : ExpByteRanged acc)
    (r : Flapjack.Exp (BitVec 64))
    (h : convAccessors ofInt fuel [] acc = some r) :
    ExpByteRanged r :=
  convAccessors_byteRanged ofInt fuel [] (by simp) acc hacc r h

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e)
    (trees : List ParseTree) (ht : ∀ t ∈ trees, ParseTreeByteRanged t)
    (es : List (Flapjack.Exp (BitVec 64)))
    (h : convExpList ofInt fuel trees = some es) :
    ∀ e ∈ es, ExpByteRanged e :=
  convExpList_byteRanged ofInt fuel hH trees ht es h

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e)
    (left opTree right : ParseTree)
    (hl : ParseTreeByteRanged left) (ho : ParseTreeByteRanged opTree)
    (hr : ParseTreeByteRanged right)
    (e : Flapjack.Exp (BitVec 64))
    (h : convComparison ofInt fuel left opTree right = some e) :
    ExpByteRanged e :=
  convComparison_byteRanged ofInt fuel hH left opTree right hl ho hr e h

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e)
    (acc : Flapjack.Exp (BitVec 64)) (hacc : ExpByteRanged acc) :
    ∀ r, convPanops ofInt fuel [] acc = some r → ExpByteRanged r :=
  convPanops_byteRanged ofInt fuel hH [] (by simp) acc hacc

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e)
    (acc : Flapjack.Exp (BitVec 64)) (hacc : ExpByteRanged acc) :
    ∀ r, convShifts ofInt fuel [] acc = some r → ExpByteRanged r :=
  convShifts_byteRanged ofInt fuel hH [] (by simp) acc hacc

example (ofInt : Int → BitVec 64) (fuel : Nat)
    (hH : ∀ g, g ≤ fuel → ∀ t, ParseTreeByteRanged t →
      ∀ e, convExp ofInt g t = some e → ExpByteRanged e)
    (acc : Flapjack.Exp (BitVec 64)) (hacc : ExpByteRanged acc) :
    ∀ r, convBinaryExps ofInt fuel [] acc = some r → ExpByteRanged r :=
  convBinaryExps_byteRanged ofInt fuel hH [] (by simp) acc hacc

example (ofInt : Int → BitVec 64) (fuel : Nat) (tree : ParseTree)
    (ht : ParseTreeByteRanged tree) :
    ∀ e, convExp ofInt fuel tree = some e → ExpByteRanged e :=
  convExp_byteRanged ofInt fuel tree ht

example {width : Nat} (l : List (Flapjack.Exp (BitVec width)))
    (h : ∀ e ∈ l, ExpByteRanged e) : ListExpByteRanged l :=
  listExpByteRanged_iff l |>.mpr h

example {width : Nat} (l : List (String × Flapjack.Exp (BitVec width)))
    (h : ∀ p ∈ l, (∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2) :
    ListFieldByteRanged l :=
  listFieldByteRanged_iff l |>.mpr h
/-! ## Declaration-conversion byte-rangedness (bead 18.3.5.8.7.1.1.1) -/

example {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat) (nt : Nonterminal)
    (r : Shape × (String × Flapjack.Exp (BitVec width)))
    (h : Flapjack.Parser.convDecForm ofInt fuel nt (ParseTree.lf Token.semiT unknownLoc) = some r) :
    ShapeByteRanged r.1 ∧ StringByteRanged r.2.1 ∧ ExpByteRanged r.2.2 :=
  convDecForm_byteRanged ofInt fuel nt _
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc) (by simp [TokenNameByteRanged])) r h

example (fuel : Nat) (r : String × Shape)
    (h : Flapjack.Parser.convExnDec fuel (ParseTree.lf Token.semiT unknownLoc) = some r) :
    StringByteRanged r.1 ∧ ShapeByteRanged r.2 :=
  convExnDec_byteRanged fuel _
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc) (by simp [TokenNameByteRanged])) r h

example {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (r : Shape × (String × (String × List (Flapjack.Exp (BitVec width)))))
    (h : Flapjack.Parser.convDecCall ofInt fuel (ParseTree.lf Token.semiT unknownLoc) = some r) :
    ShapeByteRanged r.1 ∧ StringByteRanged r.2.1 ∧ StringByteRanged r.2.2.1 ∧
      ∀ e ∈ r.2.2.2, ExpByteRanged e :=
  convDecCall_byteRanged ofInt fuel _
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc) (by simp [TokenNameByteRanged])) r h

example (r : Option (Option (Flapjack.VarKind × String)))
    (h : Flapjack.Parser.convRet (ParseTree.lf Token.semiT unknownLoc) = some r)
    (vk : Flapjack.VarKind) (name : String) (hr : r = some (some (vk, name))) :
    StringByteRanged name :=
  convRet_byteRanged _
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc) (by simp [TokenNameByteRanged])) r h vk name hr


/-- Annotation comment text is included in the byte-ranged token invariant. -/
example (text : String) (h : StringByteRanged text) :
    TokenNameByteRanged (Token.annotCommentT text) := h

example {width : Nat} (ofInt : Int → BitVec width) (fuel : Nat)
    (p : Flapjack.Prog (BitVec width))
    (h : Flapjack.Parser.convNonRecStmt ofInt fuel (ParseTree.lf Token.semiT unknownLoc) = some p) :
    ProgByteRanged p :=
  convNonRecStmt_byteRanged ofInt fuel _
    (parseTreeByteRanged_lf (token := Token.semiT) (locs := unknownLoc) (by simp [TokenNameByteRanged])) p h

/-- Location-annotation wrapping preserves byte-rangedness of a program. -/
example {width : Nat} (locations : Bool) (tree : ParseTree)
    (program : Flapjack.Prog (BitVec width)) (hp : ProgByteRanged program) :
    ProgByteRanged (addLocsAnnot locations tree program) :=
  addLocsAnnot_byteRanged locations tree hp

/-- A shape converted to its value expression is byte-ranged. -/
example {width : Nat} (ofInt : Int → BitVec width) (shape : Flapjack.Shape)
    (hs : ShapeByteRanged shape) : ExpByteRanged (Flapjack.Parser.shapeVal ofInt shape) :=
  shapeVal_byteRanged ofInt shape hs

end Flapjack.Test.ParserByteRangedParity
