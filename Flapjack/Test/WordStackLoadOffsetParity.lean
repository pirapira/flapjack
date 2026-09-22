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

/- The Cake word_to_stack offset boundary is width-independent: Load32 also
   retains the largest signed-12 positive displacement. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load32 0 1 2047 =
      some (.inst (.memOffset .load32 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

/- Cake retains the same signed-12 positive endpoint for byte and halfword
   loads; width selection is deferred to the target encoder. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load8 0 1 2047 =
      some (.inst (.memOffset .load8 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load16 0 1 2047 =
      some (.inst (.memOffset .load16 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

/- Cake retains a negative signed-12 Load displacement in the source-shaped
   MemOffset carrier as its modulo-2^64 word; Lab later interprets it as -8. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .load 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

/- The same source-shaped negative displacement is preserved for each Cake
   subword memory operator; Lab performs the later signed-12 interpretation. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load8 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .load8 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load16 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .load16 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .load32 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .load32 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
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

/- Cake's signed-12 positive endpoint is retained for subword stores too;
   the target encoder applies the width-specific instruction mapping later. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store32 0 1 2047 =
      some (.inst (.memOffset .store32 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store8 0 1 2047 =
      some (.inst (.memOffset .store8 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store16 0 1 2047 =
      some (.inst (.memOffset .store16 4 5 2047) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store8 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .store8 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store16 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .store16 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryOffsetInst
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        stackBase := 10 }
      .store32 0 1 (2 ^ 64 - 8) =
      some (.inst (.memOffset .store32 4 5 (2 ^ 64 - 8)) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

/- Cake's signed-12 negative Store displacement remains in the source-shaped
   carrier as the modulo-2^64 word (2^64 - 8); Lab later emits the signed
   -8 MemOffset form. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const (2 ^ 64 - 8)]) (.var 0) =
      some (.seq (.seq (.const 31 (2 ^ 64 - 8))
        (.arith .add 29 5 31))
        (.inst (.mem .store 4 29)) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackLocation, lookupNatInfo,
    wordStackJoin]

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

/- Cake's signed-12 negative Store displacement remains in the source-shaped
   carrier as the modulo-2^64 word (2^64 - 8); Lab later emits the signed
   -8 MemOffset form. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const (2 ^ 64 - 8)]) (.var 0) =
      some (.seq (.seq (.const 31 (2 ^ 64 - 8))
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
    wordStackCompileStoreNatNested
      { locations := [(0, .stack 3), (1, .stack 2)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const 8]) (.var 0) =
      some (.seq
        (.seq (.stackLoad 31 12)
          (.inst (.arith (.binOp .add 29 31 (.imm 8)))))
        (.seq (.stackLoad 31 13)
          (.inst (.mem .store 31 29))) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackCompileExpToRegisterNat,
    wordStackExpressionIsAtom, wordStackAtomNat, wordStackReadRegister,
    wordStackExpressionTemporaries, wordStackExpressionTemporariesExcluding,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin]

/- Subword Stores retain the same Cake spill order: reload the address into
   `wReg1`, reload the value into the independent store register, and keep the
   offset on the final memory carrier. -/
example :
    wordStackMemoryOffsetInst
      { locations := [(0, .stack 3), (1, .stack 2)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      .store32 0 1 24 =
      some (.seq (.stackLoad 31 12)
        (.seq (.stackLoad 29 13)
          (.inst (.memOffset .store32 29 31 24))) : StackProg Nat) := by
  simp [wordStackMemoryOffsetInst, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

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

/- An out-of-range positive displacement does not use Cake's MemOffset
   carrier.  `word_to_stack` materializes the constant, forms the address in
   `addressScratch`, then stages the value in the independent store scratch
   before the zero-offset store. -/
example :
    wordStackCompileStoreNatNested
      { locations := [(0, .register 4), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      (.op .add [.var 1, .const 2048]) (.var 0) =
      some (.seq
        (.seq (.const 31 2048)
          (.arith .add 29 5 31))
        (.seq (.arith .or 31 4 4)
          (.inst (.mem .store 31 29))) : StackProg Nat) := by
  simp [wordStackCompileStoreNatNested, wordStackCompileExpToRegisterNat,
    wordStackExpressionIsAtom, wordStackAtomNat, wordStackReadRegister,
    wordStackExpressionTemporaries, wordStackExpressionTemporariesExcluding,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin]

/- Cake's `wShareInst` reloads a spilled shared-memory address through
   `wReg1` before preserving the source-shaped offset carrier. -/
example :
    wordStackSharedMemoryOffsetInst
      { locations := [(0, .register 4), (1, .stack 2)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      .load8 0 1 2047 =
      some (.seq (.stackLoad 31 12)
        (.shMemOffset .load8 4 31 2047) : StackProg Nat) := by
  simp [wordStackSharedMemoryOffsetInst, wordStackSharedLoadOffsetInst,
    wordStackLocation, wordStackOffset, lookupNatInfo]

/- For a spilled shared-memory store value, Cake's `wReg2` is independent of
   the address reload and remains the source register of the final ShMemOp. -/
example :
    wordStackSharedMemoryOffsetInst
      { locations := [(0, .stack 2), (1, .register 5)]
        scratch := 31
        addressScratch := 29
        stackBase := 10 }
      .store8 0 1 2047 =
      some (.seq (.stackLoad 29 12)
        (.shMemOffset .store8 29 5 2047) : StackProg Nat) := by
  simp [wordStackSharedMemoryOffsetInst, wordStackSharedStoreOffsetInst,
    wordStackLocation, wordStackOffset, lookupNatInfo]

end Flapjack.RiscV
