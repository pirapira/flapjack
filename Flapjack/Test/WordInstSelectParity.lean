import Flapjack.RiscV.WordInstSelect

namespace Flapjack.RiscV

def cakeLoadConstAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.const (BitVec.ofNat 64 0x3f4))))

def cakeLoadVarAddress : WordProg (BitVec 64) :=
  wordInstSelectProgram 7
    (.assign 2 (.load (.var 13)))

def cakeLoadConstShape : Bool :=
  match cakeLoadConstAddress with
  | .seq (.inst (.const 7 value))
      (.inst (.mem .load 2 7)) => value == BitVec.ofNat 64 0x3f4
  | _ => false

def cakeLoadVarShape : Bool :=
  match cakeLoadVarAddress with
  | .seq (.move 0 [(7, 13)]) (.inst (.mem .load 2 7)) => true
  | _ => false

#guard cakeLoadConstShape
#guard cakeLoadVarShape

end Flapjack.RiscV
