import Flapjack.RiscV.CorrectnessLongDiv
import Flapjack.RiscV.Backend

namespace Flapjack.RiscV

/-! A concrete normalized operation remains executable when the divisor is
    register-resident or spilled.  The theorem itself carries the semantic
    quotient/remainder contract; these examples keep both lowering branches
    visible to the test build. -/

def longDivCorrectnessRegisterConfig : WordStackConfig :=
  { locations := [(0, .register 0), (3, .register 3), (4, .register 6)]
    scratch := 31
    stackBase := 10 }

def longDivCorrectnessSpillConfig : WordStackConfig :=
  { locations := [(0, .register 0), (3, .register 3), (4, .stack 2)]
    scratch := 31
    stackBase := 10 }

#guard (wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
  (.longDiv 0 3 3 0 4)).isSome

#guard (wordStackLongDivInst (α := Nat) longDivCorrectnessSpillConfig
  (.longDiv 0 3 3 0 4)).isSome

/-! The first four source fields are normalized away, as in CakeML's
    `word_to_stack` definition. -/
#guard (wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
  (.longDiv 17 18 19 20 4)).isSome

example :
    wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
        (.longDiv 17 18 19 20 4) =
      wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
        (.longDiv 0 3 3 0 4) := by
  exact wordStackLongDivInst_metadata_irrel _ _ _ _ _ _ _ _ _ _

/- The no-native-longdiv backend path follows CakeML's restoring LongDiv1
   loop and reaches the same quotient/remainder pair as StackLang.  Registers
   0 and 3 below are CakeML stack registers; the backend maps them to hardware
   x1 and x12 through riscv_names.  The numeric quotient/remainder
   129/1 is also the checked original Pancake probe result for the
   width-8 1:3 dividend divided by 2. -/
def longDivSoftwareMachineState : State 16 :=
  writeRegister
    (writeRegister
      (writeRegister (zeroState 16) 1 (BitVec.ofNat 16 259))
        12 (BitVec.ofNat 16 0))
    6 (BitVec.ofNat 16 2)

def longDivSoftwareMachineResult : Option (Word 16 × Word 16) :=
  (wordLongDivSoftwareCode (width := 16) 6).bind fun code =>
    (executeCode 512 (0 : Word 16) code longDivSoftwareMachineState).map
      (fun state => (readRegister state 1, readRegister state 12))

set_option maxRecDepth 100000 in
example :
    longDivSoftwareMachineResult =
      wordStackLongDivResult (BitVec.ofNat 16 0) (BitVec.ofNat 16 259)
        (BitVec.ofNat 16 2) := by
  decide

#guard longDivSoftwareMachineResult =
  some (BitVec.ofNat 16 129, BitVec.ofNat 16 1)

end Flapjack.RiscV
