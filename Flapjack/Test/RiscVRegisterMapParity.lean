import Flapjack.RiscV.CakeStackReseat
import Flapjack.RiscV.Lab
import Flapjack.RiscV.RegisterNames
import Flapjack.RiscV.RegisterRelabel
import Flapjack.RiscV.RegisterTransfer

/-!
# Byte preservation of the Cake register map at the Lab boundary

`Flapjack/RiscV/Lab.lean` applies the CakeML `riscv_names` map exactly once at
the Lab-to-RISC-V instruction boundary, computing `labRegisterOfNat (portToStack n)`
for every register-selection site.  For a hardware register number `n` produced
by the production pipeline, `portToStack n` is the Cake stack register whose
image under the map is `n`, so the boundary must select exactly the original
hardware register again:

* `riscvRegisterName (portToStack n) = n`
* `labRegisterOfNat (portToStack n) = registerOfNat n`

This module pins that identity for every production role register, so a future
change to `Lab.lean`, `portToStack`, or the register map cannot silently alter
the emitted bytes.  The two distinguished preimages are included: the literal
zero role (`portToStack 0 = 27`, selecting hardware `x0`) and the link role
(`portToStack 1 = 0`, selecting hardware `x1`).
-/

namespace Flapjack.Test.RiscVRegisterMapParity

open Flapjack Flapjack.RiscV

/-- Hardware register numbers used as roles by the production pipeline:
zero (`x0`), link (`x1`), store base (`x10`), current heap (`x12`), FFI service
(`x14`), carry (`x27`), special (`x28`), address (`x29`) and scratch (`x31`). -/
def productionRoleRegisters : List Nat := [0, 1, 10, 12, 14, 27, 28, 29, 31]

/-- The one-time map is a byte-preserving identity on a production role. -/
def preservesRole (name : Nat) : Bool :=
  (riscvRegisterName (portToStack name) == name) &&
    (labRegisterOfNat (portToStack name) == registerOfNat name)

/-- All production role registers are preserved by the boundary map. -/
def rolesPreserved : Bool :=
  productionRoleRegisters.all preservesRole

/-- The Cake map sends a hardware register number to `0` exactly at the internal
zero role `27`.  This computable shadow of `riscvForward_ne_zero_iff` is the
condition that discharges the transfer/relabel write-set side conditions. -/
def zeroImageExact : Bool :=
  (List.range 32).all (fun n => (riscvRegisterName n == 0) == (n == 27))

#guard zeroImageExact

/-- Every architectural register is the image of some register under the Cake
map, so the map permutes the register file.  This computable shadow of
`riscvForward_surjective` complements `zeroImageExact` and shows the one-time
relabeling loses no register. -/
def mapSurjective : Bool :=
  (List.range 32).all (fun target =>
    (List.range 32).any (fun source => riscvRegisterName source == target))

#guard mapSurjective

/-- The one-time Cake map selects the architectural zero register exactly at
the internal zero role `27`; this computable shadow of
`labRegisterOfNat_eq_zero_iff` pins the zero convention to that single role. -/
def zeroPreimageExact : Bool :=
  (List.range 32).all (fun n => (labRegisterOfNat n == some 0) == (n == 27))

#guard zeroPreimageExact

/-- The one-time Cake map has order twelve: iterating it twelve times returns
every hardware register to itself.  This computable shadow of
`iterRegisterName_twelve` / `iterForward_twelve` closes the finite inverse bound
on the register file. -/
def mapOrderTwelve : Bool :=
  (List.range 32).all (fun n => iterRegisterName 12 n == n)

#guard mapOrderTwelve

/-- The one-time Cake map is inverted by eleven further applications.  This
computable shadow of `iterRegisterName_eleven_succ` supplies the explicit
inverse step on the register file. -/
def mapInverseStep : Bool :=
  (List.range 32).all (fun n => iterRegisterName 11 (riscvRegisterName n) == n)

#guard mapInverseStep

/-- The reverse ordering also holds: one map application after eleven further
applications returns the original name.  This computable shadow of
`iterRegisterName_forward_eleven` completes the two-sided inverse step. -/
def mapForwardInverseStep : Bool :=
  (List.range 32).all (fun n => riscvRegisterName (iterRegisterName 11 n) == n)

#guard mapForwardInverseStep

example : riscvRegisterName (portToStack 0) = 0 := by decide
example : riscvRegisterName (portToStack 1) = 1 := by decide
example : riscvRegisterName (portToStack 10) = 10 := by decide
example : riscvRegisterName (portToStack 12) = 12 := by decide
example : riscvRegisterName (portToStack 14) = 14 := by decide
example : riscvRegisterName (portToStack 27) = 27 := by decide
example : riscvRegisterName (portToStack 28) = 28 := by decide
example : riscvRegisterName (portToStack 29) = 29 := by decide
example : riscvRegisterName (portToStack 31) = 31 := by decide

/-- The boundary selects exactly the original hardware registers, including the
zero (`portToStack 0 = 27`) and link (`portToStack 1 = 0`) preimages. -/
example : labRegisterOfNat (portToStack 0) = some 0 := by decide
example : labRegisterOfNat (portToStack 1) = some 1 := by decide
example : labRegisterOfNat (portToStack 10) = some 10 := by decide
example : labRegisterOfNat (portToStack 12) = some 12 := by decide
example : labRegisterOfNat (portToStack 14) = some 14 := by decide
example : labRegisterOfNat (portToStack 27) = some 27 := by decide
example : labRegisterOfNat (portToStack 28) = some 28 := by decide
example : labRegisterOfNat (portToStack 29) = some 29 := by decide
example : labRegisterOfNat (portToStack 31) = some 31 := by decide

/-- The Lab boundary lowers a constant return to the original hardware zero
operand and the original destination register, byte-for-byte. -/
example (destination value : Nat) (hvalue : value < 2 ^ 11) :
    (labCompilePlain (width := 64) (.const destination value)) =
      (labRegisterOfNat (portToStack destination)).map
        (fun register => [.ori register 0 (BitVec.ofNat 64 value)]) := by
  cases h : registerOfNat destination <;>
    simp [labCompilePlain, labRegisterOfNat_portToStack_all, h, hvalue]

/-- The one-time Cake relabeling is a bijection on the 64-bit state space,
packaging the injective and surjective boundary facts. -/
example : Function.Injective (relabelRegisters (width := 64) riscvForward) ∧
    Function.Surjective (relabelRegisters (width := 64) riscvForward) :=
  relabelRegisters_riscvForward_bijective

/-- The internal write accessor reads back the written value at its own role
whenever that role is not the hardwired zero image. -/
example (state : State 64) (value : Word 64) :
    readRegister (writeRegisterInternal riscvForward state (1 : Fin 32) value) (1 : Fin 32) =
      value :=
  readRegister_writeRegisterInternal_riscvForward_self state _ value (by decide)

/-- Every other internal read is unchanged by the internal write; only the
architectural zero role is dropped. -/
example (state : State 64) (value : Word 64) (other : Fin 32) (hne : other ≠ (1 : Fin 32)) :
    readRegister (writeRegisterInternal riscvForward state (1 : Fin 32) value) other =
      readRegister state other :=
  readRegister_writeRegisterInternal_riscvForward_other state _ other value hne

/-- The explicit transfer across the `riscv_names` map is the state relabeling
by its explicit inverse map. -/
example (state : State 64) :
    transferState state = relabelRegisters (width := 64) riscvInverse state :=
  transferState_eq_relabelRegisters_riscvInverse state

/-- Relabeling a transferred state returns the original state, so the transfer
is a two-sided inverse of the one-time Cake relabeling. -/
example (state : State 64) :
    relabelRegisters (width := 64) riscvForward (transferState state) = state :=
  relabelRegisters_riscvForward_transferState state

/-- Transferring a relabeled state returns the original state as well. -/
example (state : State 64) :
    transferState (relabelRegisters (width := 64) riscvForward state) = state :=
  transferState_relabelRegisters_riscvForward state

/-- The hardware zero slot of a transferred state is the internal register `27`,
so the concrete zero-register fact is an ordinary fact about the abstract state
rather than a hardwired assumption. -/
example (state : State 64) :
    ZeroRegister (transferState state) ↔ readRegister state (27 : Fin 32) = 0 :=
  zeroRegister_transferState_iff state

/-- Writing the hardware zero slot of a transferred state is discarded. -/
example (state : State 64) (value : Word 64) :
    writeRegister (transferState state) (0 : Fin 32) value = transferState state :=
  writeRegister_transferState_zero state value

/-- Reading an arbitrary hardware slot of a transferred state returns the
internal register named by the explicit inverse map. -/
example (state : State 64) (index : Fin 32) :
    readRegister (transferState state) index = readRegister state (riscvInverse index) :=
  readRegister_transfer state index

/-- A hardware write to an arbitrary nonzero slot of a transferred state matches
the internal write to its inverse register. -/
example (state : State 64) (index : Fin 32) (value : Word 64) (hindex : index ≠ 0) :
    writeRegister (transferState state) index value =
      transferState (writeRegisterInternal riscvForward state (riscvInverse index) value) :=
  writeRegister_transfer state index value hindex

/-- The Cake register map fixes the canonical all-zero initial state. -/
example : relabelRegisters (width := 64) riscvForward (zeroState 64) = zeroState 64 :=
  relabelRegisters_riscvForward_zeroState

/-- The `riscv_names` transfer fixes the canonical all-zero initial state. -/
example : transferState (zeroState 64) = zeroState 64 :=
  transferState_zeroState

/-- The transferred initial state still satisfies the architectural
zero-register contract. -/
example : ZeroRegister (transferState (zeroState 64)) :=
  zeroRegister_transferState_zeroState

example (state : State 64) (value : Word 64) :
    readRegister (writeRegisterInternal riscvForward state (1 : Fin 32) value) 27 =
      readRegister state 27 :=
  readRegister_writeRegisterInternal_riscvForward_zero state _ value

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("production role registers are preserved by the one-time Cake map",
        rolesPreserved),
      ("the Cake map image is zero exactly at the internal zero role",
        zeroImageExact),
      ("the Cake map permutes the architectural register file",
        mapSurjective),
      ("the Cake map selects architectural zero exactly at role 27",
        zeroPreimageExact),
      ("the Cake map has order twelve on the architectural register file",
        mapOrderTwelve),
      ("the Cake map is inverted by eleven further applications",
        mapInverseStep),
      ("the eleven-fold iterate also inverts the Cake map",
        mapForwardInverseStep) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVRegisterMapParity
