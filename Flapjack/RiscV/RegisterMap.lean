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

/-- The Cake `riscv_names` map is surjective on the architectural register
file: every register number in `0..31` is the image of some register number in
`0..31`.  Together with injectivity this makes the map a permutation of the
register file, so relabeling loses no register. -/
theorem riscvRegisterName_surjective_lt_32 {target : Nat} (htarget : target < 32) :
    ∃ name : Nat, name < 32 ∧ riscvRegisterName name = target := by
  have hcheck : ((List.range 32).all (fun candidate =>
      (List.range 32).any (fun source =>
        riscvRegisterName source == candidate))) = true := by
    decide
  have hmem : target ∈ List.range 32 := List.mem_range.mpr htarget
  have hall := List.all_eq_true.mp hcheck target hmem
  rcases List.any_eq_true.mp hall with ⟨name, hnameMem, hname⟩
  exact ⟨name, List.mem_range.mp hnameMem, by simpa [beq_iff_eq] using hname⟩

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

/-- An in-range internal stack register is selected by the one-time Cake map. -/
@[simp] theorem labRegisterOfNat_of_lt_32 {name : Nat} (h : name < 32) :
    labRegisterOfNat name =
      some ⟨riscvRegisterName name, riscvRegisterName_lt_32 h⟩ :=
  labRegisterOfNat_eq (riscvRegisterName_lt_32 h)

/-- Stack register `5` is non-architectural and maps to itself. -/
@[simp] theorem labRegisterOfNat_five : labRegisterOfNat 5 = some 5 := by decide

/-- Stack register `6` is non-architectural and maps to itself. -/
@[simp] theorem labRegisterOfNat_six : labRegisterOfNat 6 = some 6 := by decide

/-- Stack register `31` is non-architectural and maps to itself. -/
@[simp] theorem labRegisterOfNat_thirtyOne : labRegisterOfNat 31 = some 31 := by decide

/-- The internal scratch register `10` maps to hardware `27`. -/
@[simp] theorem labRegisterOfNat_ten : labRegisterOfNat 10 = some 27 := by decide

/-- The internal scratch register `11` maps to hardware `28`. -/
@[simp] theorem labRegisterOfNat_eleven : labRegisterOfNat 11 = some 28 := by decide

/-- The internal scratch register `12` maps to hardware `29`. -/
@[simp] theorem labRegisterOfNat_twelve : labRegisterOfNat 12 = some 29 := by decide

/-- The internal scratch register `13` maps to hardware `30`. -/
@[simp] theorem labRegisterOfNat_thirteen : labRegisterOfNat 13 = some 30 := by decide

/-- The Cake map is the identity above the architectural register range, so the
ABI rebase changes only registers `0`-`31`; every non-architectural internal
register is selected exactly as before. -/
theorem labRegisterOfNat_eq_registerOfNat_of_ge_32 {name : Nat} (h : 32 ≤ name) :
    labRegisterOfNat name = registerOfNat name := by
  unfold labRegisterOfNat
  rw [riscvRegisterName_id_of_ge_32 h]

/-- A register selected by the one-time Cake map is necessarily architectural. -/
theorem labRegisterOfNat_some_lt {name : Nat} {register : Fin 32}
    (h : labRegisterOfNat name = some register) : name < 32 := by
  have hriscv : riscvRegisterName name < 32 := by
    have h' : registerOfNat (riscvRegisterName name) = some register := h
    exact registerOfNat_some_lt h'
  exact lt_32_of_riscvRegisterName_lt_32 hriscv

/-- The one-time Cake map is a faithful renaming on the architectural range: it
never merges two distinct stack registers, so register-distinctness and
allocator-disjointness proofs carry over unchanged. -/
theorem labRegisterOfNat_injective {left right : Nat} {register : Fin 32}
    (hleft : labRegisterOfNat left = some register)
    (hright : labRegisterOfNat right = some register) : left = right := by
  have hleft' : registerOfNat (riscvRegisterName left) = some register := by
    simpa only [labRegisterOfNat] using hleft
  have hright' : registerOfNat (riscvRegisterName right) = some register := by
    simpa only [labRegisterOfNat] using hright
  have hname : riscvRegisterName left = riscvRegisterName right :=
    registerOfNat_injective hleft' hright' rfl
  exact riscvRegisterName_injective_lt_32
    (lt_32_of_riscvRegisterName_lt_32 (registerOfNat_some_lt hleft'))
    (lt_32_of_riscvRegisterName_lt_32 (registerOfNat_some_lt hright'))
    hname

/-- Read the value of an internal Cake stack register from a hardware-indexed
state through the one-time `riscv_names` map.  This is the register lookup the
rebased Backend correctness lemmas use: the internal name is resolved to its
hardware index exactly once and then read from the concrete register file. -/
def readRegisterInternal {width : Nat} (state : State width) (name : Nat) :
    Option (Word width) :=
  (labRegisterOfNat name).map (readRegister state)

/-- Reading an internal register whose name is out of architectural range
yields nothing. -/
@[simp] theorem readRegisterInternal_of_none {width : Nat} (state : State width)
    {name : Nat} (h : labRegisterOfNat name = none) :
    readRegisterInternal state name = none := by
  simp [readRegisterInternal, h]

/-- Reading an internal register resolves the name through the Cake map and then
reads the resulting hardware register. -/
@[simp] theorem readRegisterInternal_of_some {width : Nat} (state : State width)
    {name : Nat} {register : Fin 32} (h : labRegisterOfNat name = some register) :
    readRegisterInternal state name = readRegister state register := by
  simp [readRegisterInternal, h]

/-- A successful internal read is exactly a `labRegisterOfNat` resolution
followed by a hardware read. -/
theorem readRegisterInternal_eq_some_iff {width : Nat} (state : State width)
    (name : Nat) (value : Word width) :
    readRegisterInternal state name = some value ↔
      ∃ register, labRegisterOfNat name = some register ∧
        readRegister state register = some value := by
  unfold readRegisterInternal
  cases h : labRegisterOfNat name <;> simp

/-- Write the value of an internal Cake stack register into a hardware-indexed
state through the one-time `riscv_names` map.  This is the write counterpart of
`readRegisterInternal`: the internal name is resolved to its hardware index
exactly once and then written to the concrete register file.  Names outside the
architectural range are ignored, and `writeRegister` already write-protects the
hardware zero register. -/
def writeRegisterInternalNat {width : Nat} (state : State width) (name : Nat)
    (value : Word width) : State width :=
  (labRegisterOfNat name).elim state (fun register => writeRegister state register value)

/-- Writing an internal register whose name is out of architectural range is a
no-op. -/
@[simp] theorem writeRegisterInternalNat_of_none {width : Nat} (state : State width)
    {name : Nat} (h : labRegisterOfNat name = none) (value : Word width) :
    writeRegisterInternalNat state name value = state := by
  simp [writeRegisterInternalNat, h]

/-- Writing an internal register resolves the name through the Cake map and then
writes the resulting hardware register. -/
@[simp] theorem writeRegisterInternalNat_of_some {width : Nat} (state : State width)
    {name : Nat} {register : Fin 32} (h : labRegisterOfNat name = some register)
    (value : Word width) :
    writeRegisterInternalNat state name value = writeRegister state register value := by
  simp [writeRegisterInternalNat, h]

end Flapjack.RiscV
