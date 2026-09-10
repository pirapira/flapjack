import Flapjack.RiscV.WordToStack

/-! Regression coverage for the CakeML `LocValue` lowering boundary. -/

namespace Flapjack.RiscV

example :
    wordStackLocValue
        { locations := [(7, .register 5)], scratch := 31, stackBase := 10 }
        7 20 =
      some (.locValue 5 20 0 : StackProg Nat) := by
  simp [wordStackLocValue, wordStackLocation, lookupNatInfo]

example :
    wordStackLocValue
        { locations := [(7, .stack 2)], scratch := 31, stackBase := 10 }
        7 20 =
      some (.seq (.locValue 31 20 0) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordStackLocValue, wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(7, .register 5)], scratch := 31, stackBase := 10 }
        (.locValue 7 20) =
      some (.locValue 5 20 0 : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackLocValue, wordStackLocation,
    lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(7, .stack 2)], scratch := 31, stackBase := 10 }
        (.locValue 7 20) =
      some (.seq (.locValue 31 20 0) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackLocValue, wordStackLocation,
    wordStackOffset, lookupNatInfo]

end Flapjack.RiscV
