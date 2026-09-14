import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserConsumeTokParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:54`, `consume_tok_def`.
    `P.consume` is the existing source-shaped typed counterpart: a matching
    token consumes one input and contributes no parse-tree child; a mismatch
    leaves the input untouched and also contributes no child. -/
def token : Token := .keywordT .skipK
def other : Token := .keywordT .retK

def successGuard : Bool :=
  match P.consume token "skip" (PState.ofToks [(token, unknownLoc)]) with
  | (some [], state) => state.remaining == 0 && state.toks == []
  | _ => false

def mismatchGuard : Bool :=
  match P.consume token "skip" (PState.ofToks [(other, unknownLoc)]) with
  | (none, state) => state.remaining == 1 && state.toks == [(other, unknownLoc)]
  | _ => false

#eval successGuard && mismatchGuard
#guard successGuard
#guard mismatchGuard

end Flapjack.Test.ParserConsumeTokParity
