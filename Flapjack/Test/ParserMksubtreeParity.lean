import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserMksubtreeParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:49`, `mksubtree_def`. -/
def childLoc : Locs := { start := .posn 3 2, stop := .posn 3 6 }

def emptyGuard : Bool :=
  match P.mkSubtree .prog [] with
  | [.nd .prog [] loc] => loc == unknownLoc
  | _ => false

def childGuard : Bool :=
  match P.mkSubtree .prog [.lf (.keywordT .skipK) childLoc] with
  | [.nd .prog [.lf (.keywordT .skipK) loc] nodeLoc] =>
      loc == childLoc && nodeLoc == childLoc
  | _ => false

#eval emptyGuard && childGuard
#guard emptyGuard
#guard childGuard

end Flapjack.Test.ParserMksubtreeParity
