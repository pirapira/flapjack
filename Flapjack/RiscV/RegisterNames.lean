import Flapjack.RiscV.Backend

/-!
# CakeML RISC-V register names

The original CakeML RISC-V backend renames stack-level register numbers to
hardware registers through the `riscv_names` finite map; see
`Flapjack.RiscV.RegisterMap` for the map itself and its lemmas.

Stack register `0` is the link register, `1`-`4` are the first argument and
return registers (hardware `a0`-`a3`), and stack register `27` is the hardware
zero register.  All other stack registers map to themselves.
-/

namespace Flapjack.RiscV

/-- CakeML's stack-register convention for the RISC-V target: stack register
`27` is the hardware zero register, `0` is the link register, and `1`-`4` are
the first argument/return registers `a0`-`a3`. -/
abbrev linkStackRegister : Nat := 0

/-! ## CakeML stack-convention register assignments for the backend config

The port's backend configuration currently stores hardware register numbers
directly (scratch `31`, address scratch `29`, special scratch `28`, carry
scratch `27`, stack pointer `20`, stack base `21`, store base `10`, current heap
`12`, zero `0`).  To apply `riscv_names` exactly once at encoding we re-express
each of those roles as the CakeML *stack* register whose image under the map is
the hardware register the port already uses.  The lemmas below record the image
of every assignment, so the config can be reseated without changing emitted
hardware registers. -/

/-- Stack register for the hardware zero register (`x0`). -/
abbrev cakeZeroRegister : Nat := 27

/-- Stack register for the link register (`ra`, `x1`). -/
abbrev cakeLinkRegister : Nat := 0

/-- Stack register for the first argument/return word (`a0`, `x10`). -/
abbrev cakeArgumentBase : Nat := 1

/-- Stack register the port currently uses as its general scratch (`x31`). -/
abbrev cakeScratchRegister : Nat := 31

/-- Stack register for the stack-pointer role (`x20`). -/
abbrev cakeStackPointer : Nat := 20

/-- Stack register for the stack-base role (`x21`). -/
abbrev cakeStackBase : Nat := 21

/-- Stack register that maps to the address-scratch hardware register (`x29`). -/
abbrev cakeAddressScratch : Nat := 12

/-- Stack register that maps to the special-scratch hardware register (`x28`). -/
abbrev cakeSpecialScratch : Nat := 11

/-- Stack register that maps to the carry-scratch hardware register (`x27`). -/
abbrev cakeCarryScratch : Nat := 10

/-- Stack register for the store-constant base (`x10`), which coincides with the
first argument/return word. -/
abbrev cakeStoreBase : Nat := 1

/-- Stack register that maps to the compile-time current-heap register (`x12`). -/
abbrev cakeCurrHeap : Nat := 3

@[simp] theorem riscvRegisterName_cakeZeroRegister :
    riscvRegisterName cakeZeroRegister = 0 := rfl

@[simp] theorem riscvRegisterName_cakeLinkRegister :
    riscvRegisterName cakeLinkRegister = 1 := rfl

@[simp] theorem riscvRegisterName_cakeArgumentBase :
    riscvRegisterName cakeArgumentBase = 10 := rfl

@[simp] theorem riscvRegisterName_cakeScratchRegister :
    riscvRegisterName cakeScratchRegister = 31 := rfl

@[simp] theorem riscvRegisterName_cakeStackPointer :
    riscvRegisterName cakeStackPointer = 20 := rfl

@[simp] theorem riscvRegisterName_cakeStackBase :
    riscvRegisterName cakeStackBase = 21 := rfl

@[simp] theorem riscvRegisterName_cakeAddressScratch :
    riscvRegisterName cakeAddressScratch = 29 := rfl

@[simp] theorem riscvRegisterName_cakeSpecialScratch :
    riscvRegisterName cakeSpecialScratch = 28 := rfl

@[simp] theorem riscvRegisterName_cakeCarryScratch :
    riscvRegisterName cakeCarryScratch = 27 := rfl

@[simp] theorem riscvRegisterName_cakeStoreBase :
    riscvRegisterName cakeStoreBase = 10 := rfl

@[simp] theorem riscvRegisterName_cakeCurrHeap :
    riscvRegisterName cakeCurrHeap = 12 := rfl

theorem riscvRegisterName_eq_zero_iff {name : Nat} (h : name < 32) :
    riscvRegisterName name = 0 ↔ name = 27 := by
  constructor
  · intro hzero
    have hcheck : (List.range 32).all (fun candidate =>
        (riscvRegisterName candidate != 0) || (candidate == 27)) = true := by
      decide
    have heval := List.all_eq_true.mp hcheck name (List.mem_range.mpr h)
    simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at heval
    rcases heval with hne | htwentySeven
    · exact absurd hzero hne
    · exact htwentySeven
  · intro htwentySeven
    subst htwentySeven
    exact (by decide : riscvRegisterName 27 = 0)

/-- The CakeML `riscv_names` register map lifted to `Fin 32`.  This is the
`forward` function used when relabeling the register file: an internal Cake
stack register is stored at the hardware index it names.  Under the Cake stack
convention the internal zero register is stack register `27`, which this map
sends to hardware `x0`. -/
def riscvForward (register : Fin 32) : Fin 32 :=
  ⟨riscvRegisterName register.val, riscvRegisterName_lt_32 register.isLt⟩

@[simp] theorem riscvForward_val (register : Fin 32) :
    (riscvForward register).val = riscvRegisterName register.val := rfl

/-- The lifted `riscv_names` map is injective on the hardware register file,
so relabeling preserves distinctness of registers. -/
theorem riscvForward_injective : Function.Injective riscvForward := by
  intro left right hsame
  apply Fin.ext
  exact riscvRegisterName_injective_lt_32 left.isLt right.isLt
    (by simpa [riscvForward] using congrArg Fin.val hsame)

/-- The lifted `riscv_names` map sends a register to hardware `x0` exactly when
that register is the Cake stack zero register `27`.  This is the precondition
for the zero-image-aware internal write. -/
theorem riscvForward_eq_zero_iff {register : Fin 32} :
    riscvForward register = 0 ↔ register.val = 27 := by
  constructor
  · intro hzero
    have hvalue : riscvRegisterName register.val = 0 := by
      simpa [riscvForward] using congrArg Fin.val hzero
    exact (riscvRegisterName_eq_zero_iff register.isLt).mp hvalue
  · intro htwentySeven
    apply Fin.ext
    simp [riscvForward, htwentySeven]

end Flapjack.RiscV
