import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserMkleafParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:40`, `mkleaf_def`. -/
def keywordGuard : Bool :=
  match P.mkLeaf (.keywordT .skipK, unknownLoc) with
  | [.lf (.keywordT .skipK) loc] => loc == unknownLoc
  | _ => false

def identifierLoc : Locs :=
  { start := .posn 2 3, stop := .posn 2 4 }

def identifierGuard : Bool :=
  match P.mkLeaf (.identT "name", identifierLoc) with
  | [.lf (.identT "name") loc] => loc == identifierLoc
  | _ => false

#eval keywordGuard && identifierGuard
#guard keywordGuard
#guard identifierGuard

end Flapjack.Test.ParserMkleafParity
