import Flapjack.RiscV.WordToStack

/-! Cake's `wReg1` reloads a spilled address through the first allocator
    register.  These two shapes pin the corresponding offset-load StackLang
    forms, including a spilled destination. -/

namespace Flapjack.RiscV

/- Cake's `wInst` preserves the address offset for every ordinary memory
   operator (`word_to_stackScript.sml:137-163`).  Keep the subword forms on
   the same StackLang carrier as the word load/store forms. -/

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load 0 1 8 =
      some (.inst (.memOffset .load 4 5 8) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

/- Cake's signed-12 positive endpoint remains attached to the memory
   instruction; the later target encoder, not word_to_stack, decides whether
   it is encodable. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load 0 1 2047 =
      some (.inst (.memOffset .load 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store 0 1 2047 =
      some (.inst (.memOffset .store 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load8 0 1 8 =
      some (.inst (.memOffset .load8 4 5 8) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackCompileLoadNatNested
      { locations := [(0, .stack 2), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      0 (.op .add [.var 1, .const 8]) =
      some (.seq (.inst (.memOffset .load 31 5 8))
        (.stackStore 31 12) : StackProg Nat) := by
  simp [wordStackCompileLoadNatNested, wordStackLoadOffsetInst,
    wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load16 0 1 8 =
      some (.inst (.memOffset .load16 4 5 8) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load32 0 1 8 =
      some (.inst (.memOffset .load32 4 5 8) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store 0 1 8 =
      some (.inst (.memOffset .store 4 5 8) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store32 0 1 12 =
      some (.inst (.memOffset .store32 4 5 12) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store8 0 1 12 =
      some (.inst (.memOffset .store8 4 5 12) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store16 0 1 12 =
      some (.inst (.memOffset .store16 4 5 12) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

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

/- The source-shaped address path retains Cake's `Addr base offset` carrier
   before the final store instead of materialising an unrelated address
   sequence. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const 8]) (.var 0) =
      some (.seq (.seq (.const 31 8)
        (.arith .add 29 5 31))
        (.inst (.mem .store 4 29)) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackLocation, lookupNatInfo,
    wordStackJoin]

/- A spilled Store value still follows Cake's address/value staging: the
   address is formed first, then the value is reloaded through `wReg2`. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .stack 2), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const 8]) (.var 0) =
      some (.seq (.inst (.arith (.binOp .add 29 5 (.imm 8))))
        (.seq (.stackLoad 31 12)
          (.inst (.mem .store 31 29))) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackCompileExpToRegisterNat,
    wordStackExpressionIsAtom, wordStackAtomNat, wordStackReadRegister,
    wordStackExpressionTemporaries, wordStackExpressionTemporariesExcluding,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin]

/- The dual spill shape reloads the address through `wReg1` and preserves the
   register-resident value through the independent store scratch. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .stack 2)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const 8]) (.var 0) =
      some (.seq
        (.seq (.stackLoad 31 12)
          (.inst (.arith (.binOp .add 29 31 (.imm 8)))))
        (.seq (.arith .or 31 4 4)
          (.inst (.mem .store 31 29))) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackCompileExpToRegisterNat,
    wordStackExpressionIsAtom, wordStackAtomNat, wordStackReadRegister,
    wordStackExpressionTemporaries, wordStackExpressionTemporariesExcluding,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin]

example :
    wordStackCompileLoadNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      0 (.op .add [.var 1, .const 8]) =
      some (.inst (.memOffset .load 4 5 8) : StackProg Nat) := by
  simp [wordStackCompileLoadNatNested, wordStackLoadOffsetInst,
    wordStackLocation, wordStackOffset, lookupNatInfo]

/- Cake's subtraction-shaped address keeps the same source/target carrier;
   the subtraction operator is applied in the reserved address register. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .sub [.var 1, .const 8]) (.var 0) =
      some (.seq (.seq (.const 31 8)
        (.arith .sub 29 5 31))
        (.inst (.mem .store 4 29)) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackLocation, lookupNatInfo,
    wordStackJoin]

end Flapjack.RiscV
