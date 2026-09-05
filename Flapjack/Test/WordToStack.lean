import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness

-- FFI ABI regressions are kept here with the other Word-to-Stack tests.

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
        { locations := [(0, .stack 2), (1, .stack 3),
            (2, .stack 4), (3, .stack 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat) =
      some (.seq (.stackLoad 31 14)
        (.seq (.stackLoad 29 15)
          (.seq (.inst (.arith (.longMul 28 31 31 29)))
            (.seq (.stackStore 28 12) (.stackStore 31 13)))) : StackProg Nat) := by
  simp [wordToStackProg, wordToStackInst, wordStackArithInst,
    wordStackLongMulInst, wordStackLongMulLocationsSafe,
    wordStackLongMulLocationSafe, wordStackLongMulMoveToPhysical,
    wordStackLongMulMoveFromPhysical, wordStackLocation, wordStackOffset,
    wordStackJoin, wordSpecialArithLocationsSafe, lookupNatInfo]

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5)],
        scratch := 31, stackBase := 10, addressScratch := 29 }
    let state : WordStackMachineState 8 :=
      { registers := fun _ => 0,
        stack := fun offset =>
          if offset = 14 then BitVec.ofNat 8 3
          else if offset = 15 then BitVec.ofNat 8 4 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    (evalWordStackMachine state
      ((wordToStackProg config
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat)).getD .skip)).map
      (fun state =>
        (wordStackMachineValue config state 0,
          wordStackMachineValue config state 1)) =
      some (some (BitVec.ofNat 8 0), some (BitVec.ofNat 8 12)) := by
  native_decide

example :
    let state : State 8 :=
      writeRegister
        (writeRegister
          (writeRegister (zeroState 8) 29 255) 28 1) 27 1
    let final := executeInstructions state
      [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
        .add 27 27 31, .sltu 31 27 31, .or 28 28 31]
    (readRegister final 27, readRegister final 28) =
      (BitVec.ofNat 8 1, BitVec.ofNat 8 1) := by
  native_decide

example [NeZero width] (state : State width)
    (zero : readRegister state 0 = 0) :
    (readRegister
        (executeInstructions state
          [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
            .add 27 27 31, .sltu 31 27 31, .or 28 28 31]) 27,
      readRegister
        (executeInstructions state
          [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
            .add 27 27 31, .sltu 31 27 31, .or 28 28 31]) 28) =
      addCarryWords (readRegister state 29) (readRegister state 28)
        (readRegister state 27) := by
  apply executeInstructions_addCarry_general state 27 28 29 28 27 zero
  all_goals decide

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5), (4, .stack 6)],
        scratch := 31, stackBase := 10, addressScratch := 29,
        specialScratch := 28, carryScratch := 27 }
    wordToStackProg config
      ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat) =
      some (.seq (.stackLoad 29 14)
        (.seq (.stackLoad 28 15)
          (.seq (.stackLoad 27 16)
            (.seq (.inst (.arith (.addCarry 27 28 29 28 27)))
              (.seq (.stackStore 27 12) (.stackStore 28 13))))) : StackProg Nat) := by
  simp [wordToStackProg, wordToStackInst, wordStackArithInst,
    wordStackAddCarryInst, wordStackAddCarryLocationSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset,
    wordSpecialArithLocationsSafe, lookupNatInfo]

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5), (4, .stack 6)],
        scratch := 31, stackBase := 10, addressScratch := 29,
        specialScratch := 28, carryScratch := 27 }
    let state : WordStackMachineState 8 :=
      { registers := fun _ => 0,
        stack := fun offset =>
          if offset = 14 then BitVec.ofNat 8 255
          else if offset = 15 then BitVec.ofNat 8 1
          else if offset = 16 then BitVec.ofNat 8 1 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    (evalWordStackMachine state
      ((wordToStackProg config
        ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat)).getD .skip)).map
      (fun state =>
        (wordStackMachineValue config state 0,
          wordStackMachineValue config state 1)) =
      some (some (BitVec.ofNat 8 1), some (BitVec.ofNat 8 1)) := by
  native_decide

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
        { locations := [(2, .register 4), (3, .stack 2),
            (4, .register 6), (5, .register 7)],
          scratch := 31, stackBase := 10 }
        ((.ffi "sum" 2 3 4 5 []) : WordProg Nat) =
      some (.seq (.arith .or 10 4 4)
        (.seq (.stackLoad 11 12)
          (.seq (.arith .or 12 6 6)
            (.seq (.arith .or 13 7 7)
              (.ffi "sum" 10 11 12 13 0))))) := by
  simp [wordToStackProg, wordStackFfi, wordStackFfiSourcesSafe,
    wordStackFfiSourceSafe, wordStackFfiRegisterSafe, wordStackFfiMove,
    wordStackLocation,
    wordStackOffset, lookupNatInfo, wordStackJoin]

example (state final : WordStackMachineState 8)
    (heval : (wordStackFfiMove
      { locations := [(2, .register 4)], scratch := 31, stackBase := 10 }
      2 10).bind (evalWordStackMachine state) = some final) :
    final.registers 10 =
      wordStackMachineValue
        { locations := [(2, .register 4)], scratch := 31, stackBase := 10 }
        state 2 := by
  apply evalWordStackMachine_ffi_move_preserves_value
    (sourceLocation := .register 4)
  · native_decide
  · decide
  · exact heval

example (state final : WordStackMachineState 8)
    (heval : (wordStackFfiMove
      { locations := [(2, .stack 2)], scratch := 31, stackBase := 10 }
      2 10).bind (evalWordStackMachine state) = some final) :
    final.registers 10 =
      wordStackMachineValue
        { locations := [(2, .stack 2)], scratch := 31, stackBase := 10 }
        state 2 := by
  apply evalWordStackMachine_ffi_move_preserves_value
    (sourceLocation := .stack 2)
  · native_decide
  · decide
  · exact heval

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
    simp [wordToStackProg, wordStackReturnCode, wordStackMovesToPhysical,
    wordStackMoveToPhysical, wordStackMovesFromPhysical,
    wordStackMoveFromPhysical, wordStackLocation, lookupNatInfo]

example :
    (wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21 }
        ((.call none (some 7) [0] none) : WordProg Nat)).map
        (fun program => match program with
          | .seq (.arith .or 2 5 5) _ => true
          | _ => false) = some true := by
  native_decide

example :
    (wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21, handlerLabel := 30 }
        ((.call none (some 7) [0] (some (1, .raise 0))) : WordProg Nat)).isSome =
      true := by
  simp [wordToStackProg, wordStackReturnCode, wordStackMovesToPhysical,
    wordStackMoveToPhysical, wordStackMovesFromPhysical,
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

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.memory := by
  apply evalWordStackMachine_load_preserves_value
    (destinationLocation := .register 4) (addressLocation := .register 5)
  · rfl
  · rfl
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.memory := by
  apply evalWordStackMachine_load_preserves_value
    (destinationLocation := .stack 2) (addressLocation := .stack 3)
  · rfl
  · rfl
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.memory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_store_preserves_memory
    (config := config)
    (state := state) (final := final) (source := 0) (address := 1)
    (sourceLocation := .register 4) (addressLocation := .register 5)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config]) (hsafe := by simp [config, wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.memory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 2), (1, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_store_preserves_memory
    (config := config)
    (state := state) (final := final) (source := 0) (address := 1)
    (sourceLocation := .stack 2) (addressLocation := .stack 3)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config]) (hsafe := by simp [config, wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (dividendValue divisorValue : Word width)
    (hdividendValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some dividendValue)
    (hdivisorValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (heval : (wordStackDivInst
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 1 2).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_div_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (dividend := 1) (divisor := 2)
    (destinationLocation := .register 4)
    (dividendLocation := .register 5) (divisorLocation := .register 6)
    (dividendValue := dividendValue) (divisorValue := divisorValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividend := by simp [config, wordStackLocation, lookupNatInfo])
    (hdivisor := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividendValue := by simpa [config] using hdividendValue)
    (hdivisorValue := by simpa [config] using hdivisorValue)
    (hdivisorNonzero := hdivisorNonzero)
    (hscratch := by simp [config])
    (hdestinationSafe := by simp [config, wordStackDivLocationSafe])
    (hdividendSafe := by simp [config, wordStackDivLocationSafe])
    (hdivisorSafe := by simp [config, wordStackDivLocationSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (dividendValue divisorValue : Word width)
    (hdividendValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some dividendValue)
    (hdivisorValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (heval : (wordStackDivInst
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 1 2).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_div_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (dividend := 1) (divisor := 2)
    (destinationLocation := .stack 1)
    (dividendLocation := .stack 2) (divisorLocation := .stack 3)
    (dividendValue := dividendValue) (divisorValue := divisorValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividend := by simp [config, wordStackLocation, lookupNatInfo])
    (hdivisor := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividendValue := by simpa [config] using hdividendValue)
    (hdivisorValue := by simpa [config] using hdivisorValue)
    (hdivisorNonzero := hdivisorNonzero)
    (hscratch := by simp [config])
    (hdestinationSafe := by simp [config, wordStackDivLocationSafe])
    (hdividendSafe := by simp [config, wordStackDivLocationSafe])
    (hdivisorSafe := by simp [config, wordStackDivLocationSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileBinaryNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .add (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineBinOp .add leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_binary_assignment
    (config := config) (state := state) (final := final)
    (operator := .add) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .register 4)
    (leftLocation := .register 5) (rightLocation := .register 6)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileBinaryNat
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .xor (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineBinOp .xor leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_binary_assignment
    (config := config) (state := state) (final := final)
    (operator := .xor) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .stack 1)
    (leftLocation := .stack 2) (rightLocation := .stack 3)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileShiftNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .lsl (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineShift .lsl leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shift_assignment
    (config := config) (state := state) (final := final)
    (operator := .lsl) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .register 4)
    (leftLocation := .register 5) (rightLocation := .register 6)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileShiftNat
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .asr (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineShift .asr leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shift_assignment
    (config := config) (state := state) (final := final)
    (operator := .asr) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .stack 1)
    (leftLocation := .stack 2) (rightLocation := .stack 3)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackSharedMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.sharedMemory := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shared_load_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (address := 1)
    (destinationLocation := .register 4) (addressLocation := .register 5)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hscratch := by simp [config])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackSharedMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.sharedMemory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 2), (1, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shared_store_preserves_memory
    (config := config) (state := state) (final := final)
    (source := 0) (address := 1)
    (sourceLocation := .stack 2) (addressLocation := .stack 3)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config])
    (hsafe := by simp [config, wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      some (.inst (.arith (.longMul 4 5 6 7)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulInst, wordStackLongMulLocationsSafe,
    wordStackLongMulLocationSafe, wordStackLongMulMoveToPhysical,
    wordStackLongMulMoveFromPhysical, wordStackLocation, wordStackJoin,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      some (.inst (.arith (.addCarry 4 5 6 7 8)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackAddCarryInst, wordStackAddCarryLocationSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 4), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 31), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLocation, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .register 10), (1, .register 2),
            (2, .register 3), (3, .register 4)],
          scratch := 31, stackBase := 10 }
        ((.ffi "sum" 0 1 2 3 []) : WordProg Nat) = none := by
  native_decide

end Flapjack.RiscV
