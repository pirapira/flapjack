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

/- Cake's `remove_dead` tracks `nlive` globals backwards: an earlier
   `Set globals (Var 7)` is dead once a later write to the same global is
   retained.  This is `word_allocScript.sml:952-961`, distinct from ordinary
   local-variable dead assignment removal. -/
def deadGlobalOverwrite : WordProg Nat :=
  .seq (.set (.globals : WordStore Nat) (.var 7))
    (.set (.globals : WordStore Nat) (.var 8))

def deadGlobalOverwriteGuard : Bool :=
  match wordRemoveDeadProgram deadGlobalOverwrite with
  | .set .globals (.var 8) => true
  | _ => false

#guard deadGlobalOverwriteGuard

end Flapjack.Test.WordDeadCodeParity
