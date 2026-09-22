import Flapjack.RiscV.WordInstSelect

namespace Flapjack.RiscV

def cakeLoadConstAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.const (BitVec.ofNat 64 0x3f4))))

def cakeLoadVarAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.var 13)))

def cakeLoadPositiveOffsetAddress : Bool :=
  match wordInstSelectProgram (α := BitVec 64) 7
      (.assign 2 (.load (.op .add
        [.var 13, .const (BitVec.ofNat 64 8)]))) with
  | .seq (.move 0 [(7, 13)])
      (.inst (.memOffset .load 2 7 offset)) =>
      offset == BitVec.ofNat 64 8
  | _ => false

def cakeLoadNegativeOffsetAddress : Bool :=
  match wordInstSelectProgram (α := BitVec 64) 7
      (.assign 2 (.load (.op .add
        [.var 13, .const (BitVec.ofNat 64 (2 ^ 64 - 8))]))) with
  | .seq (.move 0 [(7, 13)])
      (.inst (.memOffset .load 2 7 offset)) =>
      offset == BitVec.ofNat 64 (2 ^ 64 - 8)
  | _ => false

def cakeLoadOutOfRangeAddress : Bool :=
  match wordInstSelectProgram (α := Nat) 7
      (.assign 2 (.load (.op .add [.var 13, .const 4096]))) with
  | .seq
      (.seq
        (.seq (.move 0 [(7, 13)]) (.inst (.const 8 4096)))
        (.inst (.arith (.binOp .add 7 7 (.reg 8)))))
      (.inst (.mem .load 2 7)) => true
  | _ => false

def cakeNonImmediateAnd : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 40 (.op .and [.var 2, .const (BitVec.ofNat 64 0xFFFFFFFF)]))

def cakeLoadConstShape : Bool :=
  match cakeLoadConstAddress with
  | .seq (.inst (.const 7 value))
      (.inst (.mem .load 2 7)) => value == BitVec.ofNat 64 0x3f4
  | _ => false

def cakeLoadVarShape : Bool :=
  match cakeLoadVarAddress with
  | .seq (.move 0 [(7, 13)]) (.inst (.mem .load 2 7)) => true
  | _ => false

def cakeLoadVarOffsetShape : Bool :=
  match wordInstSelectProgram (α := Nat) 7
      (.assign 2 (.load (.op .add [.var 13, .const 8]))) with
  | .seq (.move 0 [(7, 13)])
      (.inst (.memOffset .load 2 7 8)) => true
  | _ => false

/- Cake's `hw_offset_ok` is `offset_ok 0`, so unlike a target execution trap
   it does not impose even alignment on the selector's halfword immediate. -/
def cakeLoadOddHalfwordOffset : Bool :=
  match wordInstSelectProgram (α := Nat) 7
      (.shareInst .load16 10
        (.op .add [.var 13, .const 9])) with
  | .seq (.move 0 [(7, 13)])
      (.shareInst .load16 10 (.op .add [.var 7, .const 9])) => true
  | _ => false

def cakeStoreOddHalfwordOffset : Bool :=
  match wordInstSelectProgram (α := BitVec 64) 7
      (.shareInst .store16 10
        (.op .add [.var 13, .const (BitVec.ofNat 64 9)])) with
  | .seq (.move 0 [(7, 13)])
      (.shareInst .store16 10
        (.op .add [.var 7, .const (BitVec.ofNat 64 9)])) => true
  | _ => false

def cakeWideBinopStatementShape : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .and [.var 18, .const (2 ^ 60)])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .and 5 23 (.reg 24))))) =>
      value == 2 ^ 60
  | _ => false

/- Cake's `valid_imm` accepts signed-12-bit logical immediates and the
   selector must keep the boundary value in the immediate carrier. -/
def cakeLogicalImmediateBoundary : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .and [.var 18, .const 2047])) with
  | .seq (.move 0 [(23, 18)])
      (.inst (.arith (.binOp .and 5 23 (.imm 2047)))) => true
  | _ => false

/- The first value outside Cake's signed-12-bit immediate range is
   materialized in the selector temporary before the logical operation. -/
def cakeLogicalImmediateFirstMaterialized : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .and [.var 18, .const 2048])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .and 5 23 (.reg 24))))) =>
      value == 2048
  | _ => false

/- Cake applies the same signed-12-bit `valid_imm` boundary to OR. -/
def cakeOrLogicalImmediateBoundary : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .or [.var 18, .const 2047])) with
  | .seq (.move 0 [(23, 18)])
      (.inst (.arith (.binOp .or 5 23 (.imm 2047)))) => true
  | _ => false

def cakeOrLogicalImmediateFirstMaterialized : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .or [.var 18, .const 2048])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .or 5 23 (.reg 24))))) =>
      value == 2048
  | _ => false

/- Cake applies the same signed-12-bit `valid_imm` boundary to XOR. -/
def cakeXorLogicalImmediateBoundary : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .xor [.var 18, .const 2047])) with
  | .seq (.move 0 [(23, 18)])
      (.inst (.arith (.binOp .xor 5 23 (.imm 2047)))) => true
  | _ => false

def cakeXorLogicalImmediateFirstMaterialized : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .xor [.var 18, .const 2048])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .xor 5 23 (.reg 24))))) =>
      value == 2048
  | _ => false

/- Cake materializes a large positive `Add` constant after the modular
   negative-immediate retry fails (`word_instScript.sml:262-275`). -/
def cakeWideAddMaterializesConstant : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .add [.var 18, .const (2 ^ 60)])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .add 5 23 (.reg 24))))) =>
      value == 2 ^ 60
  | _ => false

/- Cake's RISC-V `valid_imm` accepts the two's-complement Sub operand -2047
   (word pattern 2^64-2047), whose encoder emits ADDI +2047. -/
def cakeSubNegativeImmediateBoundary : Bool :=
  match wordInstSelectAtom (α := Nat) 23
      (.op .sub [.var 18, .const (2 ^ 64 - 2047)]) with
  | (.seq (.move 0 [(23, 18)])
      (.inst (.arith (.binOp .sub 23 23 (.imm value)))), .var 23) =>
      value == 2 ^ 64 - 2047
  | _ => false

/- The strict Cake lower endpoint rejects -2048 for Sub and materializes it. -/
def cakeSubNegativeImmediateExcluded : Bool :=
  match wordInstSelectAtom (α := Nat) 23
      (.op .sub [.var 18, .const (2 ^ 64 - 2048)]) with
  | (.seq (.seq (.move 0 [(23, 18)])
      (.inst (.const 24 value)))
      (.inst (.arith (.binOp .sub 23 23 (.reg 24)))), .var 23) =>
      value == 2 ^ 64 - 2048
  | _ => false

/- Cake's RISC-V `valid_imm` includes the signed lower endpoint for Add but
   excludes it for Sub (`riscv_targetScript.sml:riscv_config_def`).  Thus the
   Add-immediate retry for `x + 2048` must not turn into the invalid `Sub -2048`
   form; Cake materializes 2048 and uses a register Add instead. -/
def cakeAddNegativeEndpointMaterializes : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .add [.var 18, .const 2048])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .add 5 23 (.reg 24))))) =>
      value == 2048
  | _ => false

def cakeSharedByteOffsetMaterializesConstant : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.shareInst .store8 10
        (.op .add [.var 12, .const 2684420096])) with
  | .seq
      (.seq
        (.seq (.move 0 [(23, 12)]) (.inst (.const 24 value)))
        (.inst (.arith (.binOp .add 23 23 (.reg 24)))))
      (.shareInst .store8 10 (.var 23)) =>
      value == 2684420096
  | _ => false

/- Cake's RISC-V `hw_offset_ok` is `offset_ok 0`, so odd halfword offsets
   remain valid and must stay in the shared-memory address carrier. -/
def cakeSharedOddHalfwordOffset : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.shareInst .store16 10
        (.op .add [.var 12, .const 9])) with
  | .seq (.move 0 [(23, 12)])
      (.shareInst .store16 10
        (.op .add [.var 23, .const 9])) => true
  | _ => false

/- The same Cake offset predicate applies independently of memory width. -/
def cakeSharedLoad32PositiveBoundary : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.shareInst .load32 10
        (.op .add [.var 12, .const 2047])) with
  | .seq (.move 0 [(23, 12)])
      (.shareInst .load32 10
        (.op .add [.var 23, .const 2047])) => true
  | _ => false

def cakeSharedStore32NegativeBoundary : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.shareInst .store32 10
        (.op .add [.var 12, .const (2 ^ 64 - 8)])) with
  | .seq (.move 0 [(23, 12)])
      (.shareInst .store32 10
        (.op .add [.var 23, .const offset])) => offset == 2 ^ 64 - 8
  | _ => false

/- Cake's `inst_select_exp` selects the non-heap operand into the fresh
   temporary before emitting the current-heap operation. -/
def cakeCurrentHeapOr : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 2 (.op .or [.lookup .currHeap, .const 1])) with
  | .seq (.inst (.const 23 value)) (.opCurrHeap .or 2 23) => value == 1
  | _ => false

def cakeConstCurrentHeapXor : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 2 (.op .xor [.const 1000, .lookup .currHeap])) with
  | .seq (.inst (.const 23 value)) (.opCurrHeap .xor 2 23) => value == 1000
  | _ => false

def cakeBitVecConstCurrentHeapXor : Bool :=
  match wordInstSelectProgram (α := BitVec 64) 23
      (.assign 2 (.op .xor [.const (BitVec.ofNat 64 1000), .lookup .currHeap])) with
  | .seq (.inst (.const 23 value)) (.opCurrHeap .xor 2 23) =>
      value == BitVec.ofNat 64 1000
  | _ => false

def cakeNestedConstCurrentHeapXor : Bool :=
  match wordInstSelectAtom (α := BitVec 64) 23
      (.op .xor [.lookup .currHeap, .const (BitVec.ofNat 64 1000)]) with
  | (.seq (.inst (.const 23 value)) (.opCurrHeap .xor 23 23), .var 23) =>
      value == BitVec.ofNat 64 1000
  | _ => false

/- Cake's word_simp materializes a non-atomic source Store address before
   word_inst sees the Store.  The selector therefore receives `Var temp` and
   emits a zero-offset Mem; the source/output regression secp_accel fixture
   exercises this ordering (word_instScript.sml:383-427). -/
def cakeWordSimpStoreShape : Bool :=
  match wordInstSelectProgram (α := Nat) 7
      (.store (.var 13) 10) with
  | .seq (.move 0 [(7, 13)])
      (.inst (.mem .store 10 7)) => true
  | _ => false

/-! Independent Cake `inst_select_def` Store oracle for the unresolved
    selector/allocator carrier boundary.  These are the exact Word shapes
    from `cakeml/compiler/backend/word_instScript.sml:389-401`; they are kept
    separate from `wordInstSelectProgram` because the current source-shaped
    pipeline intentionally preserves the baseline artifacts while the
    downstream carrier integration is still being repaired. -/
def cakeStorePositiveOffsetOracle : WordProg Nat :=
  .seq (.move 0 [(7, 13)])
    (.inst (.memOffset .store 10 7 8))

def cakeStoreNegativeOffsetOracle : WordProg Nat :=
  .seq (.move 0 [(7, 13)])
    (.inst (.memOffset .store 10 7 (2 ^ 64 - 8)))

def cakeStoreOutOfRangeOffsetOracle : WordProg Nat :=
  .seq
    (.seq (.move 0 [(7, 13)])
      (.seq (.inst (.const 8 2048))
        (.inst (.arith (.binOp .add 7 7 (.reg 8))))))
    (.inst (.mem .store 10 7))

def cakeStoreOffsetOracle : Bool :=
  (match cakeStorePositiveOffsetOracle with
   | .seq (.move 0 [(7, 13)])
       (.inst (.memOffset .store 10 7 8)) => true
   | _ => false) &&
  (match cakeStoreNegativeOffsetOracle with
   | .seq (.move 0 [(7, 13)])
       (.inst (.memOffset .store 10 7 offset)) =>
         offset == (2 ^ 64 - 8)
   | _ => false) &&
  (match cakeStoreOutOfRangeOffsetOracle with
   | .seq
       (.seq (.move 0 [(7, 13)])
         (.seq (.inst (.const 8 2048))
           (.inst (.arith (.binOp .add 7 7 (.reg 8))))))
       (.inst (.mem .store 10 7)) => true
   | _ => false)

/- The checked standalone Cake Store boundary agrees with the three exact
   `inst_select_def` shapes above.  The production source-shaped selector is
   intentionally not rewired here; that carrier migration is a separate
   downstream Word-to-Stack/allocator task. -/
def cakeStoreSelectorPositiveShape : Bool :=
  match wordInstSelectStoreCake (α := Nat) 7
      (.op .add [.var 13, .const 8]) 10 with
  | .seq (.move 0 [(7, 13)])
      (.inst (.memOffset .store 10 7 8)) => true
  | _ => false

def cakeStoreSelectorNegativeShape : Bool :=
  match wordInstSelectStoreCake (α := Nat) 7
      (.op .add [.var 13, .const (2 ^ 64 - 8)]) 10 with
  | .seq (.move 0 [(7, 13)])
      (.inst (.memOffset .store 10 7 offset)) =>
      offset == 2 ^ 64 - 8
  | _ => false

def cakeStoreSelectorOutOfRangeShape : Bool :=
  match wordInstSelectStoreCake (α := Nat) 7
      (.op .add [.var 13, .const 2048]) 10 with
  | .seq
      (.seq (.move 0 [(7, 13)])
        (.seq (.inst (.const 8 2048))
          (.inst (.arith (.binOp .add 7 7 (.reg 8))))))
      (.inst (.mem .store 10 7)) => true
  | _ => false

def cakeStoreSelectorVarShape : Bool :=
  match wordInstSelectStoreCake (α := Nat) 7 (.var 13) 10 with
  | .seq (.move 0 [(7, 13)])
      (.inst (.mem .store 10 7)) => true
  | _ => false

def cakeStoreSelectorConstShape : Bool :=
  match wordInstSelectStoreCake (α := Nat) 7 (.const 2048) 10 with
  | .seq (.inst (.const 7 2048))
      (.inst (.mem .store 10 7)) => true
  | _ => false

#guard cakeStoreSelectorPositiveShape
#guard cakeStoreSelectorNegativeShape
#guard cakeStoreSelectorOutOfRangeShape
#guard cakeStoreSelectorVarShape
#guard cakeStoreSelectorConstShape

#guard cakeLoadConstShape
#guard cakeLoadVarShape
#guard cakeLoadVarOffsetShape
#guard cakeLoadOddHalfwordOffset
#guard cakeStoreOddHalfwordOffset
#guard cakeLoadPositiveOffsetAddress
#guard cakeLoadNegativeOffsetAddress
#guard cakeLoadOutOfRangeAddress
#guard cakeWideBinopStatementShape
#guard cakeLogicalImmediateBoundary
#guard cakeLogicalImmediateFirstMaterialized
#guard cakeOrLogicalImmediateBoundary
#guard cakeOrLogicalImmediateFirstMaterialized
#guard cakeXorLogicalImmediateBoundary
#guard cakeXorLogicalImmediateFirstMaterialized
#guard cakeWideAddMaterializesConstant
#guard cakeSubNegativeImmediateBoundary
#guard cakeSubNegativeImmediateExcluded
#guard cakeAddNegativeEndpointMaterializes
#guard cakeSharedByteOffsetMaterializesConstant
#guard cakeSharedOddHalfwordOffset
#guard cakeSharedLoad32PositiveBoundary
#guard cakeSharedStore32NegativeBoundary
#guard cakeCurrentHeapOr
#guard cakeConstCurrentHeapXor
#guard cakeBitVecConstCurrentHeapXor
#guard cakeNestedConstCurrentHeapXor
#guard cakeWordSimpStoreShape
#guard cakeStoreOffsetOracle

#guard match cakeNonImmediateAnd with
  | .seq (.move 0 [(7, 2)])
      (.seq (.inst (.const 8 value))
        (.inst (.arith (.binOp .and 40 7 (.reg 8))))) =>
      value == BitVec.ofNat 64 0xFFFFFFFF
  | _ => false

end Flapjack.RiscV
