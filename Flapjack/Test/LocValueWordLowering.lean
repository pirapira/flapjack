import Flapjack.Word

/-! The Loop-to-Word translation must preserve LocValue code labels while
    applying the variable context to their destinations. -/

namespace Flapjack

example :
    loopToWordProg
        { vars := [(3, 10)] }
        (.locValue 3 100) =
      (.locValue 10 100 : WordProg Nat) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo]

example :
    loopToWordProg
        { vars := [(3, 10), (100, 200)] }
        (.locValue 3 100) =
      (.locValue 10 100 : WordProg Nat) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo]

end Flapjack
