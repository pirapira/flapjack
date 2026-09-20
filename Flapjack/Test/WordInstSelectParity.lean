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

def cakeWideBinopStatementShape : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 5 (.op .and [.var 18, .const (2 ^ 60)])) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.inst (.const 24 value))
        (.inst (.arith (.binOp .and 5 23 (.reg 24))))) =>
      value == 2 ^ 60
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

#guard cakeLoadConstShape
#guard cakeLoadVarShape
#guard cakeLoadPositiveOffsetAddress
#guard cakeLoadNegativeOffsetAddress
#guard cakeLoadOutOfRangeAddress
#guard cakeWideBinopStatementShape
#guard cakeWideAddMaterializesConstant
#guard cakeSharedByteOffsetMaterializesConstant

#guard match cakeNonImmediateAnd with
  | .seq (.move 0 [(7, 2)])
      (.seq (.inst (.const 8 value))
        (.inst (.arith (.binOp .and 40 7 (.reg 8))))) =>
      value == BitVec.ofNat 64 0xFFFFFFFF
  | _ => false

end Flapjack.RiscV
