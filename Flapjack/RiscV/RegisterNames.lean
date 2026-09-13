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

/-- CakeML's stack-register convention for word-level registers.

Word register `0` is the zero register, which CakeML numbers as stack register
`27` (and `riscv_names` maps back to hardware `x0`).  Every other word register
`n >= 1` is stack register `n - 1`, so word registers `2, 3, 4, 5` become the
argument/return registers `1, 2, 3, 4`, which `riscv_names` maps to `a0..a3`. -/
def stackRegisterOfWord (name : Nat) : Nat :=
  if name == 0 then cakeZeroRegister else name - 1

@[simp] theorem stackRegisterOfWord_zero : stackRegisterOfWord 0 = 27 := rfl

@[simp] theorem stackRegisterOfWord_one : stackRegisterOfWord 1 = 0 := rfl

@[simp] theorem stackRegisterOfWord_two : stackRegisterOfWord 2 = 1 := rfl

@[simp] theorem stackRegisterOfWord_three : stackRegisterOfWord 3 = 2 := rfl

@[simp] theorem stackRegisterOfWord_four : stackRegisterOfWord 4 = 3 := rfl

@[simp] theorem stackRegisterOfWord_five : stackRegisterOfWord 5 = 4 := rfl

theorem stackRegisterOfWord_lt_32 {name : Nat} (h : name < 32) :
    stackRegisterOfWord name < 32 := by
  unfold stackRegisterOfWord
  split
  · decide
  · omega

/-- Translate a word-level register number to its hardware register through
CakeML's stack-register convention and `riscv_names`. -/
def wordRegisterToRiscv (name : Nat) : Nat :=
  riscvRegisterName (stackRegisterOfWord name)

@[simp] theorem wordRegisterToRiscv_zero : wordRegisterToRiscv 0 = 0 := rfl

@[simp] theorem wordRegisterToRiscv_one : wordRegisterToRiscv 1 = 1 := rfl

@[simp] theorem wordRegisterToRiscv_two : wordRegisterToRiscv 2 = 10 := rfl

@[simp] theorem wordRegisterToRiscv_three : wordRegisterToRiscv 3 = 11 := rfl

@[simp] theorem wordRegisterToRiscv_four : wordRegisterToRiscv 4 = 12 := rfl

@[simp] theorem wordRegisterToRiscv_five : wordRegisterToRiscv 5 = 13 := rfl

theorem wordRegisterToRiscv_lt_32 {name : Nat} (h : name < 32) :
    wordRegisterToRiscv name < 32 :=
  riscvRegisterName_lt_32 (stackRegisterOfWord_lt_32 h)

/-- On the used word-register range `0..27` the stack-register convention
composed with `riscv_names` is injective, so it can act as a bijection on the
internally allocated registers.  Word register `28` is the only collision
(it shares stack register `27`, the hardware zero register, with word register
`0`) and is therefore reserved. -/
theorem wordRegisterToRiscv_injective_of_lt_28 {left right : Nat}
    (hleft : left < 28) (hright : right < 28)
    (hsame : wordRegisterToRiscv left = wordRegisterToRiscv right) :
    left = right := by
  have hcheck : (List.range 28).all (fun candidate =>
      (List.range 28).all (fun other =>
        (wordRegisterToRiscv candidate != wordRegisterToRiscv other) ||
          (candidate == other))) = true := by decide
  have ha := List.all_eq_true.mp hcheck left (List.mem_range.mpr hleft)
  have hb := List.all_eq_true.mp ha right (List.mem_range.mpr hright)
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hb
  rcases hb with hne | heq
  · exact absurd hsame hne
  · exact heq

/-- Under CakeML's `riscv_names` the only stack register that maps to the
hardware zero register `x0` is stack register `27`.  This identifies the
internal zero register of the Cake stack convention and is the precondition
needed to relabel a register file whose zero slot is not hardware index `0`. -/
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

end Flapjack.RiscV
