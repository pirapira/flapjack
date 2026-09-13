import Flapjack.RiscV.Model

/-!
# Register-file relabeling for the `riscv_names` rebase

The CakeML RISC-V backend renames word-level register numbers to hardware
register numbers through `riscv_names`.  To carry the corresponding Model and
Semantics agreement lemmas through that rebase, the register file of a
`State` is relabeled by a function from internal register names to hardware
indices.

This module defines that relabeling and proves the two facts the agreement
lemmas need: how `readRegister` and `writeRegister` commute with it.  The
write lemma needs injectivity (so that distinct internal names are distinct
hardware indices) and an agreement on which index is the hardwired zero
register.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- Relabel the register file of a state: internal register name `name` is
stored at hardware index `forward name`. -/
def relabelRegisters (forward : Fin 32 → Fin 32) (state : State width) : State width :=
  { state with registers := fun name => state.registers (forward name) }

@[simp] theorem relabelRegisters_pc (forward : Fin 32 → Fin 32) (state : State width) :
    (relabelRegisters forward state).pc = state.pc := rfl

@[simp] theorem relabelRegisters_memory (forward : Fin 32 → Fin 32) (state : State width) :
    (relabelRegisters forward state).memory = state.memory := rfl

@[simp] theorem relabelRegisters_privilege (forward : Fin 32 → Fin 32) (state : State width) :
    (relabelRegisters forward state).privilege = state.privilege := rfl

@[simp] theorem relabelRegisters_mode (forward : Fin 32 → Fin 32) (state : State width) :
    (relabelRegisters forward state).mode = state.mode := rfl

@[simp] theorem readRegister_relabel (forward : Fin 32 → Fin 32) (state : State width)
    (name : Fin 32) :
    readRegister (relabelRegisters forward state) name = readRegister state (forward name) := rfl

/-- Writing an internal register in the relabeled state is the same as writing
its hardware index in the original state, as long as the relabeling is
injective and maps the hardwired zero register onto the hardwired zero
register. -/
theorem writeRegister_relabel (forward : Fin 32 → Fin 32)
    (hinjective : Function.Injective forward) (state : State width) (name : Fin 32)
    (value : Word width) (hzero : forward name = 0 ↔ name = 0) :
    writeRegister (relabelRegisters forward state) name value =
      relabelRegisters forward (writeRegister state (forward name) value) := by
  by_cases hname : name = 0
  · subst hname
    have hforward : forward 0 = 0 := hzero.mpr rfl
    simp [writeRegister, relabelRegisters, hforward]
  · have hforwardName : forward name ≠ 0 := by
      intro hforward
      exact hname (hzero.mp hforward)
    cases state with
    | mk pc registers memory privilege mode =>
      simp only [relabelRegisters, writeRegister, hname, hforwardName, ↓reduceIte]
      congr 1
      funext current
      by_cases hcurrent : current = name
      · subst hcurrent
        simp
      · have hforwardCurrent : forward current ≠ forward name :=
          fun hsame => hcurrent (hinjective hsame)
        simp [hcurrent, hforwardCurrent]

end Flapjack.RiscV
