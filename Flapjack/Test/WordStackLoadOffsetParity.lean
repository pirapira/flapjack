import Flapjack.RiscV.WordToStack

/-! Cake's `wReg1` reloads a spilled address through the first allocator
    register.  These two shapes pin the corresponding offset-load StackLang
    forms, including a spilled destination. -/

namespace Flapjack.RiscV

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .stack 2)]
        scratch := 31
        stackBase := 10
        addressScratch := 29 }
      .load 0 1 24 =
      some (.seq (.stackLoad 31 12)
        (.inst (.memOffset .load 4 31 24)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .stack 3), (1, .stack 2)]
        scratch := 31
        stackBase := 10
        addressScratch := 29 }
      .load 0 1 24 =
      some (.seq (.stackLoad 31 12)
        (.seq (.inst (.memOffset .load 31 31 24))
          (.stackStore 31 13)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

end Flapjack.RiscV
