/-
Parity fixture for `Flapjack.Parser.getKeyword` against the direct HOL oracle
`scripts/hol-probes/pan_lexer_get_keyword_probe.out` (`panLexer$get_keyword`,
`panLexerScript.sml:115-153`).

Bead flapjack-pxn.18.3.5.8.7.1.1: the executable lexer replaced the original
keyword if-chain with the ordered `keywordTable`; these rows pin the exact
production output for every table entry plus the fallbacks.
-/
import Flapjack.Parser.Lexer

namespace Flapjack.Test.ParserKeywordParity

open Flapjack.Parser

/-- All 33 `keywordTable` keys in table order paired with their expected token. -/
private def rows : List (String × Token) :=
  [("skip", .keywordT .skipK), ("st", .keywordT .stK), ("stw", .keywordT .stwK),
   ("st8", .keywordT .st8K), ("st16", .keywordT .st16K), ("st32", .keywordT .st32K),
   ("if", .keywordT .ifK), ("else", .keywordT .elseK), ("while", .keywordT .whileK),
   ("break", .keywordT .brK), ("continue", .keywordT .contK), ("throw", .keywordT .throwK),
   ("return", .keywordT .retK), ("tick", .keywordT .ticK), ("var", .keywordT .varK),
   ("in", .keywordT .inK), ("try", .keywordT .tryK), ("catch", .keywordT .catchK),
   ("lds", .keywordT .ldsK), ("ldw", .keywordT .ldwK), ("ld8", .keywordT .ld8K),
   ("ld16", .keywordT .ld16K), ("ld32", .keywordT .ld32K), ("@base", .keywordT .baseK),
   ("@top", .keywordT .baseK), ("@biw", .keywordT .biwK), ("true", .keywordT .trueK),
   ("false", .keywordT .falseK), ("fun", .keywordT .funK), ("export", .keywordT .exportK),
   ("inline", .keywordT .inlineK), ("exception", .keywordT .exceptionK),
   ("struct", .keywordT .namedK)]

/-- Every keyword table entry maps to its exact expected token. -/
private def keywordsGuard : Bool :=
  rows.all (fun (s, expected) => getKeyword s == expected)

/-- Fallbacks: empty string, `@`-foreign, ordinary identifier, lone `@`. -/
private def fallbackGuard : Bool :=
  (match getKeyword "" with | .lexErrorT _ => true | _ => false)
    && (getKeyword "@ffi" == .foreignIdent "ffi")
    && (getKeyword "abc" == .identT "abc")
    && (getKeyword "@" == .identT "@")

/-- No keyword entry is empty or accidental. -/
private def countGuard : Bool := rows.length == 33

def parityGuard : Bool := keywordsGuard && fallbackGuard && countGuard

#eval parityGuard
#guard parityGuard

example : getKeyword "skip" = Token.keywordT Keyword.skipK := by decide
example : getKeyword "@top" = Token.keywordT Keyword.baseK := by decide
example : getKeyword "struct" = Token.keywordT Keyword.namedK := by decide
example : getKeyword "@ffi" = Token.foreignIdent "ffi" := by decide
example : getKeyword "abc" = Token.identT "abc" := by decide

end Flapjack.Test.ParserKeywordParity