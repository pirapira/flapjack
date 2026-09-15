import Flapjack.RiscV.WordUnreach

namespace Flapjack.RiscV

open Flapjack

/- Cake's `remove_unreach_test` from word_unreachScript.sml. -/
example :
    wordRemoveUnreachable
        (.seq (.move 1 [(1, 11), (2, 22), (3, 33)])
          (.move 1 [(3, 1), (2, 99)])) =
      (.move 1 [(3, 11), (2, 99), (1, 11)] : WordProg Nat) := by
  simp [wordRemoveUnreachable, wordUnreachSimpSeq,
    wordUnreachMergeMoves, wordUnreachAnub, wordUnreachLookup,
    lookupNatInfo]

end Flapjack.RiscV
