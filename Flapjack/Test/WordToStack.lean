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

example :
    wordToStackProg
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10 }
        ((.ite .equal 0 (.reg 1) .skip .skip) : WordProg Nat) =
      some (.seq (.seq (.stackLoad 31 12) (.stackLoad 29 13))
        (.ite .equal 31 (.reg 29) .skip .skip) : StackProg Nat) := by
  simp [wordToStackProg, wordStackConditionOperands, wordStackReadRegister,
    wordStackJoin, wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordToStackProg
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        ((.return 0 [0]) : WordProg Nat) =
      some (.seq (.seq (.stackLoad 31 12) (.arith .or 2 31 31)) (.return 2) :
        StackProg Nat) := by
  simp [wordToStackProg, wordStackReturn, wordStackMovesToPhysical,
    wordStackMoveToPhysical, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin]

example :
    wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        ((.set .currHeap (.var 0)) : WordProg Nat) =
      some (.set .currHeap 5 : StackProg Nat) := by
  simp [wordToStackProg, wordStackStoreName, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin]

example :
    wordToStackProg
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 }
        ((.shareInst .load32 0 (.var 1)) : WordProg Nat) =
      some (.shMem .load32 4 5 : StackProg Nat) := by
  simp [wordToStackProg, wordStackSharedMemoryInst,
    wordStackSharedLoadInst, wordStackLocation, lookupNatInfo]

example :
    wordToStackProg
        { locations := [], scratch := 31, stackBase := 10 }
        ((.loop [] (.break 0) []) : WordProg Nat) =
      some (.loop (.break 0) : StackProg Nat) := by
  simp [wordToStackProg]

example :
    wordToStackProg
        { locations := [], scratch := 31, stackBase := 10 }
        ((.ffi "sum" 2 3 4 5 []) : WordProg Nat) =
      some (.ffi "sum" 2 3 4 5 0 : StackProg Nat) := by
  simp [wordToStackProg, wordToStackFfi]

example :
    wordToStackProgNat
        { locations := [(0, .register 4)], scratch := 31, stackBase := 10 }
        ((.assign 0 (.const 42)) : WordProg Nat) =
      some (.const 4 42 : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackWritePhysicalNat, wordStackLocation, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        ((.assign 0 (.const 42)) : WordProg Nat) =
      some (.seq (.const 31 42) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.op .add [.var 1, .const 3])) : WordProg Nat) =
      some (.seq (.const 29 3)
        (.seq (.arith .add 31 5 29) (.stackStore 31 12)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileBinaryNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.load (.var 1))) : WordProg Nat) =
      some (.seq (.stackLoad 29 13)
        (.seq (.inst (.mem .load 31 29)) (.stackStore 31 12)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileLoadNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.shift .lsl (.var 1) (.var 2))) : WordProg Nat) =
      some (.shift .lsl 4 5 6 : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileShiftNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.shift .lsr (.var 1) (.const 3))) : WordProg Nat) =
      some (.seq (.stackLoad 31 13)
        (.seq (.const 29 3)
          (.seq (.shift .lsr 31 31 29) (.stackStore 31 12))) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileShiftNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10,
          addressScratch := 29 }
        ((.store (.const 100) 0) : WordProg Nat) =
      some (.seq (.const 29 100) (.inst (.mem .store 5 29)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileStoreNat,
    wordStackAtomNat, wordStackJoin, wordStackReadRegister,
    wordStackLocation, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        ((.set (.temp 4) (.const 7)) : WordProg Nat) =
      some (.seq (.const 31 7) (.set (.temp 4) 31) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackSetNat, wordStackAtomNat,
    wordStackJoin, wordStackStoreNameNat]

example :
    (evalWordStackMachine
        { registers := fun register => if register = 5 then 9 else 0,
          stack := fun _ => 0,
          stores := fun _ => 0,
          memory := fun _ => 0,
          sharedMemory := fun _ => 0 }
        ((wordToStackProgNat
          { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
          ((.assign 0 (.const 42)) : WordProg Nat)).getD .skip)).bind
      (fun state => wordStackMachineValue
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        state 0) =
      some (BitVec.ofNat 8 42) := by
  native_decide

example :
    (wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21 }
        ((.call (some ([0], [])) (some 7) [0] none) : WordProg Nat)).isSome =
      true := by
  simp [wordToStackProg, wordStackReturnCode, wordStackMovesFromPhysical,
    wordStackMoveFromPhysical, wordStackLocation, lookupNatInfo]

example :
    (wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21, handlerLabel := 30 }
        ((.call none (some 7) [0] (some (1, .raise 0))) : WordProg Nat)).isSome =
      true := by
  simp [wordToStackProg, wordStackReturnCode, wordStackMovesFromPhysical,
    wordStackMoveFromPhysical, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordToStackCallWithHandler, wordToStackRaise,
    stackSeq, stackArgs, stackMove, stackPushHandler, stackHandlerArgs,
    wordStackJoin]

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

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      some (.inst (.arith (.longMul 4 5 6 7)) : StackProg Nat) := by
  simp [wordStackArithInst, wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      some (.inst (.arith (.addCarry 4 5 6 7 8)) : StackProg Nat) := by
  simp [wordStackArithInst, wordStackLocation, lookupNatInfo]

end Flapjack.RiscV
