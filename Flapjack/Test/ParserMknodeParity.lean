import Flapjack.Parser.ParseTree

namespace Flapjack.Test.ParserMknodeParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:44`, `mknode_def`. -/
def firstLoc : Locs := { start := .posn 2 3, stop := .posn 2 7 }
def secondLoc : Locs := { start := .posn 2 9, stop := .posn 2 12 }

def emptyGuard : Bool :=
  match P.mkNode .prog [] with
  | .nd .prog [] loc => loc == unknownLoc
  | _ => false

def singleGuard : Bool :=
  match P.mkNode .prog [.lf (.keywordT .skipK) firstLoc] with
  | .nd .prog [.lf (.keywordT .skipK) loc] nodeLoc =>
      loc == firstLoc && nodeLoc == firstLoc
  | _ => false

def multipleGuard : Bool :=
  match P.mkNode .prog
      [.lf (.keywordT .skipK) firstLoc, .lf (.keywordT .retK) secondLoc] with
  | .nd .prog
      [.lf (.keywordT .skipK) first, .lf (.keywordT .retK) second] nodeLoc =>
      first == firstLoc && second == secondLoc &&
      nodeLoc == { start := .posn 2 3, stop := .posn 2 12 }
  | _ => false

#eval emptyGuard && singleGuard && multipleGuard
#guard emptyGuard
#guard singleGuard
#guard multipleGuard

end Flapjack.Test.ParserMknodeParity
