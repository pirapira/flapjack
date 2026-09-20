import Flapjack.RiscV.WordDeadCode

namespace Flapjack.Test.WordDeadCodeParity

open Flapjack Flapjack.RiscV

def raiseTail : WordProg Nat :=
  .seq (.raise 2)
    (.seq (.move 0 [(413, 0)]) (.return 389 [2]))

def raiseTailGuard : WordProg Nat → Bool
  | .seq (.raise 2) (.return 389 [2]) => true
  | _ => false

#guard raiseTailGuard (wordRemoveDeadProgram raiseTail)

end Flapjack.Test.WordDeadCodeParity
