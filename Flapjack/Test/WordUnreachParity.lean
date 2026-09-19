import Flapjack.RiscV.WordUnreach

namespace Flapjack.RiscV

open Flapjack

/- The accumulator-backed Cake sequence flattening retains left-to-right
   order before the adjacent-move fold. -/
def wordCopyUnreachPartsOrderGuard : Bool :=
  match wordCopyUnreachParts
      (.seq (.seq (.assign 1 (.const 1)) (.assign 2 (.const 2)))
        (.seq (.assign 3 (.const 3)) (.assign 4 (.const 4))) : WordProg Nat) with
  | [.assign 1 (.const 1), .assign 2 (.const 2),
     .assign 3 (.const 3), .assign 4 (.const 4)] => true
  | _ => false

#guard wordCopyUnreachPartsOrderGuard

def wordCopyUnreachMergeOrderGuard : Bool :=
  match wordCopyUnreachMergeMoves [(1, 11), (2, 22), (3, 33)]
      [(3, 1), (2, 99)] with
  | [(3, 11), (2, 99), (1, 11)] => true
  | _ => false

#guard wordCopyUnreachMergeOrderGuard

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
