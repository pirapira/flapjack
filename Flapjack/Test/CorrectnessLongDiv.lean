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

example :
    wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
        (.longDiv 17 18 19 20 4) =
      wordStackLongDivInst (α := Nat) longDivCorrectnessRegisterConfig
        (.longDiv 0 3 3 0 4) := by
  exact wordStackLongDivInst_metadata_irrel _ _ _ _ _ _ _ _ _ _

/-! Cake's `wReg1 n5` does not reject a divisor that aliases either fixed
    LongDiv source register.  The emitted operation still reads the divisor
    before writing the quotient/remainder, so these two source-shaped cases
    must remain concrete rather than being silently dropped. -/

def longDivFixedSourceAliasConfig : WordStackConfig :=
  { locations := [(0, .register 0), (3, .register 3), (4, .register 0)]
    scratch := 31
    stackBase := 10 }

def longDivFixedRemainderAliasConfig : WordStackConfig :=
  { locations := [(0, .register 0), (3, .register 3), (4, .register 3)]
    scratch := 31
    stackBase := 10 }

example :
    wordStackLongDivInst (α := Nat) longDivFixedSourceAliasConfig
        (.longDiv 0 3 3 0 4) =
      some (.inst (.arith (.longDiv 0 3 3 0 0)) : StackProg Nat) := by
  rfl

example :
    wordStackLongDivInst (α := Nat) longDivFixedRemainderAliasConfig
        (.longDiv 0 3 3 0 4) =
      some (.inst (.arith (.longDiv 0 3 3 0 3)) : StackProg Nat) := by
  rfl

end Flapjack.RiscV
