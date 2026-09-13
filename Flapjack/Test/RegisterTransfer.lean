import Flapjack.RiscV.RegisterTransfer

/-!
# RISC-V register-transfer bridge tests

These regressions exercise the concrete CakeML `riscv_names` transfer at the
boundary between internal stack-register state and hardware-register state.
They deliberately test the two exceptional cases: the internal link register
maps to hardware `x1`, while the internal zero register `27` maps to hardware
`x0`.
-/

namespace Flapjack.Test.RegisterTransfer

open Flapjack Flapjack.RiscV

#guard (riscvForward (0 : Fin 32)).val == 1
#guard (riscvForward (1 : Fin 32)).val == 10
#guard (riscvForward (27 : Fin 32)).val == 0
#guard (riscvInverse (0 : Fin 32)).val == 27
#guard (riscvInverse (10 : Fin 32)).val == 1

def sampleState : State 64 :=
  { pc := 0
    registers := fun register => BitVec.ofNat 64 (register.val + 100)
    memory := fun _ => 0
    privilege := .machine
    mode := .mbare }

#guard (readRegister (transferState sampleState) (riscvForward (5 : Fin 32))).toNat == 105
#guard (readRegister (transferState sampleState) (0 : Fin 32)).toNat == 127

example (state : State width) (name : Fin 32) :
    readRegister (transferState state) (riscvForward name) =
      readRegister state name := by
  exact readRegister_transfer_forward state name

example (state : State width) (name : Fin 32) (value : Word width) :
    writeRegister (transferState state) (riscvForward name) value =
      transferState (writeRegisterInternal riscvForward state name value) := by
  exact writeRegister_transfer_forward state name value

end Flapjack.Test.RegisterTransfer
