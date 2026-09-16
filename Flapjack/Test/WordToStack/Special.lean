import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness

namespace Flapjack.RiscV

/- Cake's wInst stages a spilled binary destination through the first
   temporary while retaining register-resident operands.  This is the small
   regression that used to make the fn87 source-to-RISC-V pipeline fail. -/
example :
    wordStackArithInst
        { locations := [(0, .stack 2), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        (.binOp .or 0 1 (.reg 2)) =
      some (.seq (.arith .or 31 5 6) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset, lookupNatInfo]

/- A spilled left register operand is loaded before the register-operand
   arithmetic and the result is written back using Cake's wRegWrite1. -/
example :
    wordStackArithInst
        { locations := [(0, .stack 2), (1, .stack 3), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        (.shift .lsl 0 1 (.reg 2)) =
      some (.seq (.stackLoad 31 13)
        (.seq (.inst (.arith (.shift .lsl 31 31 (.reg 6))))
          (.stackStore 31 12)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      some (.inst (.arith (.longMul 4 5 6 7)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulInst,
    wordStackLocation, 
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 4),
            (2, .register 3), (3, .register 5)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      some (.inst (.arith (.longMul 4 4 3 5)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulInst, wordStackLongMulAliasLocationsSafe,
    wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      some (.inst (.arith (.addCarry 4 5 6 7 8)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackAddCarryInst,
    
    wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 6),
            (2, .register 7), (3, .register 8)],
          scratch := 31, stackBase := 10 } (.cakeAddCarry 0 1 2 3) =
      some (.inst (.arith (.cakeAddCarry 4 6 7 8)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackCakeAddCarryInst,
    wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .stack 2), (1, .stack 3),
            (2, .stack 4), (3, .stack 5)],
          scratch := 31, stackBase := 10, addressScratch := 29,
          specialScratch := 28, carryScratch := 27 } (.cakeAddCarry 0 1 2 3) =
      some (.seq (.stackLoad 29 13)
        (.seq (.stackLoad 28 14)
          (.seq (.stackLoad 27 15)
            (.seq (.inst (.arith (.cakeAddCarry 31 29 28 27)))
              (.seq (.stackStore 31 12) (.stackStore 27 15))))) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackCakeAddCarryInst, wordStackAddCarryLocationSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 4), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulAliasLocationsSafe, wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .register 6)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      some (.inst (.arith (.longDiv 0 3 3 0 6)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .stack 2)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      some (.seq (.stackLoad 31 12)
        (.inst (.arith (.longDiv 0 3 3 0 31))) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .register 3)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 31), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulAliasLocationsSafe, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .register 10), (1, .register 2),
            (2, .register 3), (3, .register 4)],
          scratch := 31, stackBase := 10 }
        ((.ffi "sum" 0 1 2 3 ([], [])) : WordProg Nat) =
      some (.seq
        (.seq
          (.seq (.arith .or 13 4 4)
            (.arith .or 12 3 3))
          (.arith .or 11 2 2))
        (.ffi "sum" 10 11 12 13 0)) := by
  simp [wordToStackProgNat, wordStackFfi, wordStackFfiSourcesSafe,
    wordStackFfiSourceSafe, wordStackFfiRegisterSafe, wordStackLocation,
    lookupNatInfo, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMove,
    wordStackLocationMoveDestinations, wordStackLocationMoveReady,
    wordStackLocationMoveRemoveDestination, wordStackJoin]

end Flapjack.RiscV
