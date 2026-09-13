import Flapjack.RiscV.RegisterRelabel

/-!
# Transferring register files across the `riscv_names` map

`Flapjack.RiscV.RegisterNames` defines the CakeML `riscv_names` map as a
function `riscvForward : Fin 32 → Fin 32` on hardware register indices, and
`Flapjack.RiscV.RegisterRelabel` re-labels a machine state by pushing a map
through its register file.

To apply `riscv_names` exactly once at the RISC-V boundary, the production
statement carries *internal* register numbers while the machine model executes
*hardware* numbers obtained by `riscvForward`.  This file starts the bridge in
that direction: an explicit inverse `riscvInverse` together with the left and
right inverse laws, and `transferState`, which re-indexes a machine state so
that hardware slot `riscvForward name` holds the value of internal register
`name`.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- The explicit inverse of the `riscv_names` map, computed by an exhaustive
case analysis on the sixteen moved register names. -/
def riscvInverseName (name : Nat) : Nat :=
  match name with
  | 1 => 0
  | 10 => 1
  | 11 => 2
  | 12 => 3
  | 13 => 4
  | 27 => 10
  | 28 => 11
  | 29 => 12
  | 30 => 13
  | 0 => 27
  | 2 => 28
  | 3 => 29
  | 4 => 30
  | other => other

theorem riscvInverseName_lt_32 {name : Nat} (h : name < 32) :
    riscvInverseName name < 32 := by
  unfold riscvInverseName
  split <;> omega

/-- The inverse of the `riscv_names` map on the hardware register file. -/
def riscvInverse (register : Fin 32) : Fin 32 :=
  ⟨riscvInverseName register.val, riscvInverseName_lt_32 register.isLt⟩

/-- `riscvInverse` is a left inverse of `riscvForward`. -/
theorem riscvInverse_riscvForward (register : Fin 32) :
    riscvInverse (riscvForward register) = register := by
  apply Fin.ext
  have hcheck : (List.range 32).all (fun candidate =>
      riscvInverseName (riscvRegisterName candidate) == candidate) = true := by
    decide
  have heval := List.all_eq_true.mp hcheck register.val
    (List.mem_range.mpr register.isLt)
  simpa [riscvInverse, riscvForward, beq_iff_eq] using heval

/-- `riscvInverse` is a right inverse of `riscvForward`. -/
theorem riscvForward_riscvInverse (register : Fin 32) :
    riscvForward (riscvInverse register) = register := by
  apply Fin.ext
  have hcheck : (List.range 32).all (fun candidate =>
      riscvRegisterName (riscvInverseName candidate) == candidate) = true := by
    decide
  have heval := List.all_eq_true.mp hcheck register.val
    (List.mem_range.mpr register.isLt)
  simpa [riscvInverse, riscvForward, beq_iff_eq] using heval

/-- The internal Cake stack register number whose image is hardware zero. -/
theorem riscvInverse_zero : riscvInverse (0 : Fin 32) = 27 := by decide

/-- Re-index a machine state so that hardware slot `riscvForward name` holds the
value of the internal register `name`.  Concretely, hardware index `index` holds
the value of internal register `riscvInverse index`. -/
def transferState (state : State width) : State width :=
  { state with registers := fun index => state.registers (riscvInverse index) }

@[simp] theorem transferState_pc (state : State width) :
    (transferState state).pc = state.pc := rfl

@[simp] theorem transferState_memory (state : State width) :
    (transferState state).memory = state.memory := rfl

@[simp] theorem transferState_privilege (state : State width) :
    (transferState state).privilege = state.privilege := rfl

@[simp] theorem transferState_mode (state : State width) :
    (transferState state).mode = state.mode := rfl

/-- Reading hardware slot `riscvForward name` of a transferred state returns the
internal register `name`. -/
@[simp] theorem readRegister_transfer_forward (state : State width) (name : Fin 32) :
    readRegister (transferState state) (riscvForward name) = readRegister state name := by
  simp [readRegister, transferState, riscvInverse_riscvForward]

/-- The hardware zero slot of a transferred state holds the internal Cake zero
register `27`. -/
@[simp] theorem readRegister_transfer_zero (state : State width) :
    readRegister (transferState state) (0 : Fin 32) = readRegister state (27 : Fin 32) := by
  simp [readRegister, transferState, riscvInverse_zero]

/-- A hardware write to slot `riscvForward name` on a transferred state matches
the internal write to register `name` (discarded when `name` is the Cake zero
register `27`). -/
theorem writeRegister_transfer_forward (state : State width) (name : Fin 32)
    (value : Word width) :
    writeRegister (transferState state) (riscvForward name) value =
      transferState (writeRegisterInternal riscvForward state name value) := by
  by_cases hzero : riscvForward name = 0
  · simp [writeRegister, writeRegisterInternal, transferState, hzero]
  · cases state with
    | mk pc registers memory privilege mode =>
      simp only [transferState, writeRegister, writeRegisterInternal]
      rw [if_neg hzero, if_neg hzero]
      congr 1
      funext index
      by_cases hidx : index = riscvForward name
      · subst hidx
        have himage : riscvInverse (riscvForward name) = name := riscvInverse_riscvForward name
        simp [himage]
      · have hback : riscvInverse index ≠ name := by
          intro hcontra
          apply hidx
          calc index = riscvForward (riscvInverse index) := (riscvForward_riscvInverse index).symm
            _ = riscvForward name := by rw [hcontra]
        simp [hidx, hback]

end Flapjack.RiscV
