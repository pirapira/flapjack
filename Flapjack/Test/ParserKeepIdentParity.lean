import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserKeepIdentParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:72`, `keep_ident_def`. -/
def identifier : Token := .identT "name"
def other : Token := .keywordT .skipK

def successGuard : Bool :=
  match P.keepIdent (PState.ofToks [(identifier, unknownLoc)]) with
  | (some [.lf actual loc], state) =>
      actual == identifier && loc == unknownLoc && state.remaining == 0 && state.toks == []
  | _ => false

def mismatchGuard : Bool :=
  match P.keepIdent (PState.ofToks [(other, unknownLoc)]) with
  | (none, state) => state.remaining == 1 && state.toks == [(other, unknownLoc)]
  | _ => false

#eval successGuard && mismatchGuard
#guard successGuard
#guard mismatchGuard

end Flapjack.Test.ParserKeepIdentParity
