import Flapjack.RiscV.RegisterTransfer
import Flapjack.RiscV.WordToStack
import Flapjack.StackRemove

/-!
# Reseating backend configuration to CakeML's stack-register convention

The port's executable backend currently stores *hardware* RISC-V register
numbers directly in its configuration records (scratch `31`, address scratch
`29`, special scratch `28`, carry scratch `27`, zero `0`, link `1`).  The
original CakeML RISC-V target instead carries *stack* register numbers through
the backend and applies `riscv_names` exactly once at the Lab-to-RISC-V
encoding boundary (`cakeml/compiler/backend/riscv/riscv_configScript.sml`):
stack `27` is hardware `x0`, stack `0` is the link register `x1`, and stack
`1`-`4` are the first argument/return registers `a0`-`a3`.

This module records the reseating function that converts a configuration's
hardware-numbered roles into the CakeML stack numbers whose `riscv_names`
image is that same hardware register.  Applying `riscvForward` once at encoding
therefore reproduces the port's current hardware assignment, so the reseat is
byte-preserving while making the internal convention faithful to CakeML.

`riscvInverseName` (the inverse of `riscv_names`, from
`Flapjack.RiscV.RegisterTransfer`) is exactly the "hardware number to stack
number" direction needed here.
-/

namespace Flapjack.RiscV

/-- The port's internal register number for the hardware zero register. -/
abbrev portZeroRegister : Nat := 0

/-- The port's internal register number for the link register (`x1`). -/
abbrev portLinkRegister : Nat := 1

/-- The port's internal register number for the address scratch (`x29`). -/
abbrev portAddressScratch : Nat := 29

/-- The port's internal register number for the special scratch (`x28`). -/
abbrev portSpecialScratch : Nat := 28

/-- The port's internal register number for the carry scratch (`x27`). -/
abbrev portCarryScratch : Nat := 27

/-- Convert one of the port's hardware-numbered internal registers to the
CakeML stack register whose `riscv_names` image is that hardware register. -/
def portToStack (name : Nat) : Nat := riscvInverseName name

/-- Reseat a `WordStackConfig` so that the scratch-role fields carry CakeML
stack register numbers rather than hardware numbers.  All other fields are
unchanged. -/
def reseatWordStackConfig (config : WordStackConfig) : WordStackConfig :=
  { config with
      addressScratch := portToStack config.addressScratch
      specialScratch := portToStack config.specialScratch
      carryScratch := portToStack config.carryScratch }

@[simp] theorem portToStack_portZeroRegister :
    portToStack portZeroRegister = cakeZeroRegister := rfl

@[simp] theorem portToStack_portLinkRegister :
    portToStack portLinkRegister = cakeLinkRegister := rfl

@[simp] theorem portToStack_portAddressScratch :
    portToStack portAddressScratch = cakeAddressScratch := rfl

@[simp] theorem portToStack_portSpecialScratch :
    portToStack portSpecialScratch = cakeSpecialScratch := rfl

@[simp] theorem portToStack_portCarryScratch :
    portToStack portCarryScratch = cakeCarryScratch := rfl

/-- `riscv_names` sends the stack reseat of a hardware register number back to
that hardware number. -/
theorem riscvRegisterName_portToStack {name : Nat} (h : name < 32) :
    riscvRegisterName (portToStack name) = name := by
  have hval := congrArg Fin.val (riscvForward_riscvInverse (⟨name, h⟩ : Fin 32))
  simp only [riscvForward_val, riscvInverse] at hval
  simpa [portToStack] using hval

/-- Reseating the port's address scratch yields the CakeML stack register whose
`riscv_names` image is the port's hardware address scratch. -/
theorem riscvRegisterName_reseat_addressScratch (config : WordStackConfig)
    (h : config.addressScratch < 32) :
    riscvRegisterName (reseatWordStackConfig config).addressScratch =
      config.addressScratch := by
  simpa [reseatWordStackConfig] using riscvRegisterName_portToStack h

/-- Reseating the port's special scratch yields the CakeML stack register whose
`riscv_names` image is the port's hardware special scratch. -/
theorem riscvRegisterName_reseat_specialScratch (config : WordStackConfig)
    (h : config.specialScratch < 32) :
    riscvRegisterName (reseatWordStackConfig config).specialScratch =
      config.specialScratch := by
  simpa [reseatWordStackConfig] using riscvRegisterName_portToStack h

/-- Reseating the port's carry scratch yields the CakeML stack register whose
`riscv_names` image is the port's hardware carry scratch. -/
theorem riscvRegisterName_reseat_carryScratch (config : WordStackConfig)
    (h : config.carryScratch < 32) :
    riscvRegisterName (reseatWordStackConfig config).carryScratch =
      config.carryScratch := by
  simpa [reseatWordStackConfig] using riscvRegisterName_portToStack h

/-- The port's zero register is hardware `x0`, so its stack reseat is the
CakeML zero register `27`. -/
theorem portToStack_zero : portToStack portZeroRegister = 27 := rfl

/-- The port's link register is hardware `x1`, so its stack reseat is the CakeML
link register `0`.  This is the faithfulness correction: the port called the
zero register `0` and the link register `1`, whereas CakeML numbers the link
register `0` and the zero register `27`. -/
theorem portToStack_link : portToStack portLinkRegister = 0 := rfl

/-- The reseated scratch roles are pairwise distinct, so the `riscv_names`
rebase introduces no register collision among them. -/
theorem reseat_scratch_roles_distinct (config : WordStackConfig)
    (haddress : config.addressScratch = portAddressScratch)
    (hspecial : config.specialScratch = portSpecialScratch)
    (hcarry : config.carryScratch = portCarryScratch) :
    (reseatWordStackConfig config).addressScratch ≠
        (reseatWordStackConfig config).specialScratch ∧
      (reseatWordStackConfig config).addressScratch ≠
        (reseatWordStackConfig config).carryScratch ∧
      (reseatWordStackConfig config).specialScratch ≠
        (reseatWordStackConfig config).carryScratch := by
  simp only [reseatWordStackConfig]
  rw [haddress, hspecial, hcarry]
  simp [portToStack, riscvInverseName]

/-- Reseat a `StackRemoveConfig` so its heap/store roles carry CakeML stack
register numbers (store base `10`->`1`, current heap `12`->`3`, address scratch
`29`->`12`); the remaining roles already sit at fixed points of `riscv_names`. -/
def reseatStackRemoveConfig (config : StackRemoveConfig) : StackRemoveConfig :=
  { config with
      storeBase := portToStack config.storeBase
      currHeap := portToStack config.currHeap
      addressScratch := portToStack config.addressScratch }

@[simp] theorem portToStack_portStoreBase : portToStack 10 = cakeStoreBase := rfl

@[simp] theorem portToStack_portCurrHeap : portToStack 12 = cakeCurrHeap := rfl

/-- Reseating a `StackRemoveConfig` sends each role back to the original
hardware register through `riscv_names`. -/
theorem riscvRegisterName_reseat_storeBase (config : StackRemoveConfig)
    (h : config.storeBase < 32) :
    riscvRegisterName (reseatStackRemoveConfig config).storeBase =
      config.storeBase := by
  simpa [reseatStackRemoveConfig] using riscvRegisterName_portToStack h

theorem riscvRegisterName_reseat_currHeap (config : StackRemoveConfig)
    (h : config.currHeap < 32) :
    riscvRegisterName (reseatStackRemoveConfig config).currHeap =
      config.currHeap := by
  simpa [reseatStackRemoveConfig] using riscvRegisterName_portToStack h

theorem riscvRegisterName_reseat_stackRemoveAddressScratch
    (config : StackRemoveConfig) (h : config.addressScratch < 32) :
    riscvRegisterName (reseatStackRemoveConfig config).addressScratch =
      config.addressScratch := by
  simpa [reseatStackRemoveConfig] using riscvRegisterName_portToStack h

end Flapjack.RiscV
