import Flapjack.RiscV.Backend

/-!
# CakeML RISC-V register names

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
encoding.
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

/-- CakeML's stack-register convention for the RISC-V target: stack register
`27` is the hardware zero register, `0` is the link register, and `1`-`4` are
the first argument/return registers `a0`-`a3`. -/
abbrev zeroStackRegister : Nat := 27

abbrev linkStackRegister : Nat := 0

/-- Convert a CakeML stack register number to a hardware RISC-V register by
applying `riscv_names` once at the Lab-to-RISC-V encoding boundary. -/
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

/-- The port's word/stack register numbering puts its zero register at `0` and
its first argument/return word at `2`, one past CakeML's stack register `1`.
This is the translation from the port's convention to a CakeML stack register:
`0` stays the port's zero register and every other port register `name` is the
CakeML stack register `name - 1`. -/
def portRegisterToRiscv (name : Nat) : Nat :=
  if name == 0 then 0 else riscvRegisterName (name - 1)

@[simp] theorem portRegisterToRiscv_zero : portRegisterToRiscv 0 = 0 := by
  simp [portRegisterToRiscv]

/-- Port register `2` (the first argument/return word) maps to hardware `a0`. -/
@[simp] theorem portRegisterToRiscv_two : portRegisterToRiscv 2 = 10 := by
  decide

@[simp] theorem portRegisterToRiscv_three : portRegisterToRiscv 3 = 11 := by
  decide

@[simp] theorem portRegisterToRiscv_four : portRegisterToRiscv 4 = 12 := by
  decide

@[simp] theorem portRegisterToRiscv_five : portRegisterToRiscv 5 = 13 := by
  decide

@[simp] theorem portRegisterToRiscv_one : portRegisterToRiscv 1 = 1 := by
  decide

/-- The port convention is NOT injective on `0..31`: the shifted map sends both
port register `0` (the port's zero register) and port register `28` to hardware
`x0`.  Wiring the port convention in therefore requires reseating the reserved
config registers (notably `addressScratch = 29 -> x3`, `specialScratch = 28 ->
x0`, `scratch = 31 -> x4`, `carryScratch = 27`, `currHeap = 12 -> x29`) before
the map can be applied as a pure renaming. -/
theorem portRegisterToRiscv_not_injective :
    portRegisterToRiscv 0 = portRegisterToRiscv 28 := by decide

/-- The port-convention map stays inside the hardware register range wherever
`riscv_names` does. -/
theorem portRegisterToRiscv_lt_32 {name : Nat} (h : name < 32) :
    portRegisterToRiscv name < 32 := by
  unfold portRegisterToRiscv
  split
  · decide
  · have hname : name - 1 < 32 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) h
    exact riscvRegisterName_lt_32 hname

end Flapjack.RiscV
