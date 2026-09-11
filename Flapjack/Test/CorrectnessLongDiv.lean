import Flapjack.RiscV.CorrectnessLongDiv

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

end Flapjack.RiscV
