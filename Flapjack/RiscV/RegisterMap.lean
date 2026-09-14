import Flapjack.RiscV.Model

/-!
# CakeML RISC-V register name map

The original CakeML RISC-V backend renames stack-level register numbers to
hardware registers through the `riscv_names` finite map
(`cakeml/compiler/backend/riscv/riscv_configScript.sml`):

```
insert 0 1 o
  insert 1 10 o
  insert 2 11 o
  insert 3 12 o
  insert 4 13 o
  insert 10 27 o
  insert 11 28 o
  insert 12 29 o
  insert 13 30 o
  insert 27 0 o
  insert 28 2 o
  insert 29 3 o
  insert 30 4
```

Stack register `0` is the link register, `1`-`4` are the first argument and
return registers (hardware `a0`-`a3`), and stack register `27` is the hardware
zero register.  All other stack registers map to themselves.  This module
records the map so the port can apply it exactly once at Lab-to-RISC-V
encoding.  It lives below `Backend` so that instruction selection can convert
stack-numbered registers to hardware registers directly.
-/

namespace Flapjack.RiscV

/-- CakeML's `riscv_names` register map: stack register number to hardware
register number. -/
def riscvRegisterName (name : Nat) : Nat :=
  match name with
  | 0 => 1
  | 1 => 10
  | 2 => 11
  | 3 => 12
  | 4 => 13
  | 10 => 27
  | 11 => 28
  | 12 => 29
  | 13 => 30
  | 27 => 0
  | 28 => 2
  | 29 => 3
  | 30 => 4
  | other => other

@[simp] theorem riscvRegisterName_zero : riscvRegisterName 0 = 1 := rfl

@[simp] theorem riscvRegisterName_one : riscvRegisterName 1 = 10 := rfl

@[simp] theorem riscvRegisterName_two : riscvRegisterName 2 = 11 := rfl

@[simp] theorem riscvRegisterName_three : riscvRegisterName 3 = 12 := rfl

@[simp] theorem riscvRegisterName_four : riscvRegisterName 4 = 13 := rfl

@[simp] theorem riscvRegisterName_ten : riscvRegisterName 10 = 27 := rfl

@[simp] theorem riscvRegisterName_eleven : riscvRegisterName 11 = 28 := rfl

@[simp] theorem riscvRegisterName_twelve : riscvRegisterName 12 = 29 := rfl

@[simp] theorem riscvRegisterName_thirteen : riscvRegisterName 13 = 30 := rfl

@[simp] theorem riscvRegisterName_twentySeven : riscvRegisterName 27 = 0 := rfl

@[simp] theorem riscvRegisterName_twentyEight : riscvRegisterName 28 = 2 := rfl

@[simp] theorem riscvRegisterName_twentyNine : riscvRegisterName 29 = 3 := rfl

@[simp] theorem riscvRegisterName_thirty : riscvRegisterName 30 = 4 := rfl

/-- The map preserves the hardware register range. -/
theorem riscvRegisterName_lt_32 {name : Nat} (h : name < 32) :
    riscvRegisterName name < 32 := by
  unfold riscvRegisterName
  split <;> first | decide | assumption

/-- The map is injective on `0..31`, so it can be used as a register renaming
without merging distinct stack registers. -/
theorem riscvRegisterName_injective_lt_32 {left right : Nat}
    (hleft : left < 32) (hright : right < 32)
    (hsame : riscvRegisterName left = riscvRegisterName right) : left = right := by
  have hcheck : ((List.range 32).all (fun candidate =>
      (List.range 32).all (fun other =>
        (riscvRegisterName candidate != riscvRegisterName other) ||
          (candidate == other)))) = true := by
    decide
  have hleftMem : left ∈ List.range 32 := List.mem_range.mpr hleft
  have hrightMem : right ∈ List.range 32 := List.mem_range.mpr hright
  have hleftAll : ((List.range 32).all (fun other =>
        (riscvRegisterName left != riscvRegisterName other) ||
          (left == other))) = true :=
    List.all_eq_true.mp hcheck left hleftMem
  have hrightAll := List.all_eq_true.mp hleftAll right hrightMem
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hrightAll
  rcases hrightAll with hne | heq
  · exact absurd hsame hne
  · exact heq

/-- The map is the identity on register numbers `32` and above, the range the
port reserves for non-architectural values. -/
theorem riscvRegisterName_id_of_ge_32 {name : Nat} (h : 32 ≤ name) :
    riscvRegisterName name = name := by
  unfold riscvRegisterName
  split <;> first | omega | rfl

/-- A mapped register number can only be an architectural register when the
source number already is. -/
theorem lt_32_of_riscvRegisterName_lt_32 {name : Nat}
    (h : riscvRegisterName name < 32) : name < 32 := by
  by_cases hge : 32 ≤ name
  · rw [riscvRegisterName_id_of_ge_32 hge] at h
    omega
  · omega

/-! ## Stack-register-to-hardware conversion

`registerOfNat` embeds an internal register number into the architectural
register file when it is in range. `labRegisterOfNat` composes it with
`riscv_names`, applying the CakeML stack convention exactly once. Keeping these
in this low module lets the Lab-to-RISC-V boundary use the map without
depending on `Flapjack.RiscV.Backend`. -/

def registerOfNat (name : Nat) : Option (Fin 32) :=
  if h : name < 32 then some ⟨name, h⟩ else none

@[simp] theorem registerOfNat_zero : registerOfNat 0 = some 0 := by
  simp [registerOfNat]

theorem registerOfNat_some_lt {name : Nat} {register : Fin 32}
    (h : registerOfNat name = some register) : name < 32 := by
  simp only [registerOfNat] at h
  split at h <;> simp_all

theorem registerOfNat_injective {left right : Nat}
    {leftRegister rightRegister : Fin 32}
    (hleft : registerOfNat left = some leftRegister)
    (hright : registerOfNat right = some rightRegister)
    (hsame : leftRegister = rightRegister) : left = right := by
  have hleft_lt := registerOfNat_some_lt hleft
  have hright_lt := registerOfNat_some_lt hright
  have hleft_fin :
      (⟨left, hleft_lt⟩ : Fin 32) = leftRegister := by
    have h := hleft
    simp [registerOfNat, hleft_lt] at h
    exact h
  have hright_fin :
      (⟨right, hright_lt⟩ : Fin 32) = rightRegister := by
    have h := hright
    simp [registerOfNat, hright_lt] at h
    exact h
  have hfin :
      (⟨left, hleft_lt⟩ : Fin 32) = (⟨right, hright_lt⟩ : Fin 32) :=
    hleft_fin.trans (hsame.trans hright_fin.symm)
  exact congrArg Fin.val hfin

/-- Convert a CakeML *stack* register number to a hardware RISC-V register by
applying `riscv_names` once, mirroring the original CakeML backend's
`reg_names`. -/
def labRegisterOfNat (name : Nat) : Option (Fin 32) :=
  registerOfNat (riscvRegisterName name)

/-- The CakeML zero stack register maps to hardware `x0`. -/
@[simp] theorem labRegisterOfNat_zeroStack : labRegisterOfNat 27 = some 0 := by
  simp [labRegisterOfNat]

/-- The CakeML link stack register maps to hardware `x1`. -/
@[simp] theorem labRegisterOfNat_link : labRegisterOfNat 0 = some 1 := by
  decide

/-- The first argument/return stack register maps to hardware `a0`. -/
@[simp] theorem labRegisterOfNat_argument0 : labRegisterOfNat 1 = some 10 := by
  decide

@[simp] theorem labRegisterOfNat_argument1 : labRegisterOfNat 2 = some 11 := by
  decide

@[simp] theorem labRegisterOfNat_argument2 : labRegisterOfNat 3 = some 12 := by
  decide

@[simp] theorem labRegisterOfNat_argument3 : labRegisterOfNat 4 = some 13 := by
  decide

/-- The mapped register is in range whenever the stack register is. -/
theorem labRegisterOfNat_eq {name : Nat} (h : riscvRegisterName name < 32) :
    labRegisterOfNat name = some ⟨riscvRegisterName name, h⟩ := by
  simp [labRegisterOfNat, registerOfNat, h]

end Flapjack.RiscV
