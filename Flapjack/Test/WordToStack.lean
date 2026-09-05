import Flapjack.RiscV.WordToStack

namespace Flapjack.RiscV

example :
    wordStackMove
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.arith .or 4 5 5 : StackProg Nat) := by
  exact wordStackMove_registers

example :
    wordStackMove
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.arith .or 31 5 5) (.stackStore 31 12) : StackProg Nat) := by
  exact wordStackMove_register_to_spill

example :
    wordToStackProg
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 }
        ((.seq (.assign 0 (.var 1)) (.locValue 1 0)) : WordProg Nat) =
      some (.seq
        (.seq (.arith .or 31 5 5) (.stackStore 31 12))
        (.seq (.stackLoad 31 12) (.arith .or 5 31 31)) : StackProg Nat) := by
  simp [wordToStackProg, wordStackMove, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryInst
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .load32 0 1 =
      some (.seq (.stackLoad 29 12) (.inst (.mem .load32 4 29)) : StackProg Nat) := by
  exact wordStackMemoryInst_load_spill_address

example :
    wordStackMemoryInst
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .store32 0 1 =
      some (.seq (.stackLoad 29 12)
        (.seq (.stackLoad 31 13) (.inst (.mem .store32 31 29))) : StackProg Nat) := by
  exact wordStackMemoryInst_store_spill_value_and_address

example :
    wordStackDivInst
        { locations := [(0, .stack 3), (1, .stack 2), (2, .register 6)],
          scratch := 31, stackBase := 10 } 0 1 2 =
      some (.seq (.stackLoad 31 12)
        (.seq (.inst (.arith (.div 31 31 6)))
          (.stackStore 31 13)) : StackProg Nat) := by
  exact wordStackDivInst_spill_operands

example [NeZero width]
    (state final : WordStackState width)
    (heval : (wordStackMove (α := Nat)
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1).bind
      (evalWordStackBasic state) = some final) :
    wordStackValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } final 0 =
      wordStackValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } state 1 := by
  apply evalWordStackBasic_move_preserves_value
    (destinationLocation := .stack 2) (sourceLocation := .register 5)
  · rfl
  · rfl
  · simp
  · simp
  · exact heval

end Flapjack.RiscV
