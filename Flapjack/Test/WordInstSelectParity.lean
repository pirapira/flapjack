import Flapjack.RiscV.WordInstSelect

namespace Flapjack.RiscV

def cakeLoadConstAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.const (BitVec.ofNat 64 0x3f4))))

def cakeLoadVarAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.var 13)))

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

#guard cakeLoadConstShape
#guard cakeLoadVarShape
#guard cakeWideBinopStatementShape

#guard match cakeNonImmediateAnd with
  | .seq (.move 0 [(7, 2)])
      (.seq (.inst (.const 8 value))
        (.inst (.arith (.binOp .and 40 7 (.reg 8))))) =>
      value == BitVec.ofNat 64 0xFFFFFFFF
  | _ => false

end Flapjack.RiscV
