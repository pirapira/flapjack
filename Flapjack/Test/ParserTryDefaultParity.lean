import Flapjack.Parser

/-!
  `try_default_def` parity.

  Reference: `cakeml/pancake/parser/panPEGScript.sml:124-125`:

  `try_default s t = choicel [s; empty $ mkleaf (t, unknown_loc)]`.

  `P.tryDefault` is the direct source-shaped port. These checks observe both
  branches and the state behavior that matters to later parse-tree conversion:
  success keeps the successful parser's consumption and trees; failure
  backtracks to the original token stream and emits one unknown-location leaf.
  The checked-in HOL fixture `pan_peg_try_default_probe.out` records the same
  two branches at the original `parse` boundary.
-/

namespace Flapjack.Test.ParserTryDefaultParity

open Flapjack Flapjack.Parser

def token : Token := .keywordT .inlineK

def successful : P P.Trees := P.keepKw .inlineK "inline"

def failing : P P.Trees := P.keepKw .exportK "export"

def run (p : P P.Trees) : Option P.Trees × PState :=
  P.tryDefault p token
    (PState.ofToks [(token, unknownLoc), (.keywordT .funK, unknownLoc)])

-- Successful `s` wins and consumes exactly its token.
#guard match run successful with
  | (some [ParseTree.lf (.keywordT .inlineK) _], state) => state.remaining == 1
  | _ => false

-- Failed `s` is backtracked before the default branch; the default leaf has
-- unknown location and the original input remains untouched.
#guard match run failing with
  | (some [ParseTree.lf (.keywordT .inlineK) loc], state) =>
      loc == unknownLoc && state.remaining == 2 &&
      state.toks == [(token, unknownLoc), (.keywordT .funK, unknownLoc)]
  | _ => false

-- The public grammar uses the same branch for omitted function modifiers.
def sameAst {α : Type} [Repr α] (actual expected : α) : Bool :=
  reprStr actual == reprStr expected

#guard sameAst
  (Parser.parseTopDecs (fun value => value) "fun f() { skip; }").toOption
  (.some [.function { name := "f", inline := false, exported := false,
                       params := [], body := .skip, returnShape := .one }])

end Flapjack.Test.ParserTryDefaultParity
