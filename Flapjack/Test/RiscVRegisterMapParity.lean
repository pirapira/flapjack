import Flapjack.RiscV.CakeStackReseat
import Flapjack.RiscV.Lab

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
example (destination : Nat) (value : Nat) :
    (labCompilePlain (width := 64) (.const destination value)) =
      (labRegisterOfNat (portToStack destination)).map
        (fun register => [.addi register 0 (BitVec.ofNat 64 value)]) := by
  cases h : registerOfNat destination <;>
    simp [labCompilePlain, labRegisterOfNat_portToStack_all, h]

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("production role registers are preserved by the one-time Cake map",
        rolesPreserved),
      ("the Cake map image is zero exactly at the internal zero role",
        zeroImageExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVRegisterMapParity