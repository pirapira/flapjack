import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserKeepAnnotParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:78`, `keep_annot_def`. -/
def annotation : Token := .annotCommentT "comment"
def other : Token := .keywordT .skipK

def successGuard : Bool :=
  match P.keepAnnot (PState.ofToks [(annotation, unknownLoc)]) with
  | (some [.lf actual loc], state) =>
      actual == annotation && loc == unknownLoc && state.remaining == 0 && state.toks == []
  | _ => false

def mismatchGuard : Bool :=
  match P.keepAnnot (PState.ofToks [(other, unknownLoc)]) with
  | (none, state) => state.remaining == 1 && state.toks == [(other, unknownLoc)]
  | _ => false

#eval successGuard && mismatchGuard
#guard successGuard
#guard mismatchGuard

end Flapjack.Test.ParserKeepAnnotParity
