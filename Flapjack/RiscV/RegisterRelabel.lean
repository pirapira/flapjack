import Flapjack.RiscV.RegisterNames

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

@[simp] theorem relabelRegisters_id (state : State width) :
    relabelRegisters id state = state := by
  cases state
  simp [relabelRegisters]

/-- Relabeling twice by `g` then `f` is one relabeling by their composition
`fun name => g (f name)`.  This lets the Cake map be applied at a single
boundary instead of being threaded twice through the relation. -/
theorem relabelRegisters_comp (f g : Fin 32 → Fin 32) (state : State width) :
    relabelRegisters f (relabelRegisters g state) =
      relabelRegisters (fun name => g (f name)) state := by
  cases state
  simp [relabelRegisters]

/-- Relabeling by a surjective map is injective on states: the register file is
the only relabeled component, and surjectivity makes the image cover every
hardware register, so equal images force equal register files. -/
theorem relabelRegisters_injective (forward : Fin 32 → Fin 32)
    (hsurj : Function.Surjective forward) :
    Function.Injective (relabelRegisters (width := width) forward) := by
  intro s1 s2 h
  have h' := h
  cases s1 with
  | mk pc1 regs1 mem1 privilege1 mode1 =>
    cases s2 with
    | mk pc2 regs2 mem2 privilege2 mode2 =>
      simp only [relabelRegisters, State.mk.injEq] at h'
      obtain ⟨hpc, hregs, hmem, hprivilege, hmode⟩ := h'
      subst hpc
      subst hmem
      subst hprivilege
      subst hmode
      congr 1
      funext hardware
      obtain ⟨name, rfl⟩ := hsurj hardware
      exact congrFun hregs name

/-- The concrete Cake register map relabels the register file injectively,
because it is surjective on the 32 hardware registers. -/
theorem relabelRegisters_riscvForward_injective :
    Function.Injective (relabelRegisters (width := width) riscvForward) :=
  relabelRegisters_injective riscvForward riscvForward_surjective

/-- The one-time Cake relabeling is invertible: applying the eleven-fold iterate
after it returns the original state.  This supplies the explicit inverse needed
to undo the relabeling on the register file. -/
theorem relabelRegisters_riscvForward_comp_inverse (state : State width) :
    relabelRegisters riscvForward (relabelRegisters (iterForward 11) state) =
      state := by
  rw [relabelRegisters_comp]
  have hid : (fun register => iterForward 11 (riscvForward register)) = id := by
    funext register
    exact iterForward_eleven_forward register
  rw [hid, relabelRegisters_id]

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

/-- Writing an internal register when the hardwired zero register is not at
internal index `0`.  Under the CakeML numbering the zero register is stack
register `27`, whose hardware image is `0`; this variant skips the write when
the register's hardware image is the zero register, matching the hardware
`writeRegister` behavior. -/
def writeRegisterInternal (forward : Fin 32 → Fin 32) (state : State width)
    (name : Fin 32) (value : Word width) : State width :=
  if forward name = 0 then state
  else
    { state with
      registers := fun current => if current = name then value else state.registers current }

/-- Writing an internal register under the relabeling is the same as writing
its hardware image in the original state, for any injective relabeling.  This
is the zero-image-aware companion of `writeRegister_relabel` and does not
assume that the internal zero register sits at internal index `0`. -/
theorem writeRegisterInternal_relabel (forward : Fin 32 → Fin 32)
    (hinjective : Function.Injective forward) (state : State width) (name : Fin 32)
    (value : Word width) :
    writeRegisterInternal forward (relabelRegisters forward state) name value =
      relabelRegisters forward (writeRegister state (forward name) value) := by
  by_cases hzeroImage : forward name = 0
  · simp [writeRegisterInternal, relabelRegisters, hzeroImage, writeRegister]
  · have hwrite : writeRegister state (forward name) value =
        { state with
          registers := fun current =>
            if current = forward name then value else state.registers current } := by
      simp [writeRegister, hzeroImage]
    rw [hwrite]
    cases state with
    | mk pc registers memory privilege mode =>
      simp only [writeRegisterInternal, relabelRegisters, hzeroImage, ↓reduceIte]
      congr 1
      funext current
      by_cases hcurrent : current = name
      · subst hcurrent
        simp
      · have hforwardCurrent : forward current ≠ forward name :=
          fun hsame => hcurrent (hinjective hsame)
        simp [hcurrent, hforwardCurrent]

/-- Reading an internal register in the `riscvForward`-relabeled state is
reading its `riscv_names` hardware index in the original state. -/
theorem readRegister_relabel_riscvForward (state : State width) (name : Fin 32) :
    readRegister (relabelRegisters riscvForward state) name =
      readRegister state (riscvForward name) :=
  readRegister_relabel riscvForward state name

/-- Writing an internal register in the `riscvForward`-relabeled state is the
same as writing its `riscv_names` hardware index in the original state.  This
instantiates the zero-image-aware write with the concrete CakeML register map;
its internal zero register is stack register `27`, whose image is `x0`. -/
theorem writeRegisterInternal_relabel_riscvForward (state : State width) (name : Fin 32)
    (value : Word width) :
    writeRegisterInternal riscvForward (relabelRegisters riscvForward state) name value =
      relabelRegisters riscvForward (writeRegister state (riscvForward name) value) :=
  writeRegisterInternal_relabel riscvForward riscvForward_injective state name value

/-- The CakeML internal zero register `27` is not stored by the internal write,
matching the hardware hardwired zero. -/
@[simp] theorem writeRegisterInternal_riscvForward_zero (state : State width)
    (value : Word width) :
    writeRegisterInternal riscvForward state 27 value = state := by
  have hzero : riscvForward (27 : Fin 32) = 0 :=
    (riscvForward_eq_zero_iff (register := 27)).mpr (by decide)
  simp [writeRegisterInternal, hzero]

end Flapjack.RiscV
