import Flapjack.RiscV.WordToStack

namespace Flapjack.Test.CakeTailCallSsaParity

open Flapjack Flapjack.RiscV

def cakeTailCallSsa : WordProg Nat :=
  (wordSsaRenameProgramWithLoops []
      ({ current := [(0, 45), (12, 93)], next := 100 } : WordSsaState)
      (.call none (some 67) [0, 12] none)).2

def cakeTailCallSsaShape : Bool :=
  match cakeTailCallSsa with
  | .seq (.move 1 [(0, 45), (2, 93)])
      (.call none (some 67) [0, 2] none) => true
  | _ => false

#guard cakeTailCallSsaShape

def cakeReturnSuffixConfig : WordStackConfig :=
  { locations := [], scratch := 31, stackBase := 0, abiRegisterCount := 12 }

def cakeReturnSuffixShape : Bool :=
  wordStackReturnStackSuffix cakeReturnSuffixConfig [2] == [] &&
    stackNumReturnSlots 12 (wordStackReturnStackSuffix cakeReturnSuffixConfig [2]) == 0 &&
    wordStackReturnStackSuffix cakeReturnSuffixConfig (List.range 14) == [12, 13]

#guard cakeReturnSuffixShape

end Flapjack.Test.CakeTailCallSsaParity
