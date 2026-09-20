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

/- Cake's remove_dead drops an If after both branches become Skip, while
   retaining the condition in the backward live set. -/
def deadIfBranchesGuard : Bool :=
  match wordDeadCodeAux
      (.ite .equal 4 (.imm 0) (.skip : WordProg Nat) .skip) [9] [] with
  | (.skip, live) => live == [9, 4]
  | _ => false

#guard deadIfBranchesGuard

end Flapjack.Test.WordDeadCodeParity
