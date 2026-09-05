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
