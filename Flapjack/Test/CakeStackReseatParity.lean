import Flapjack.RiscV.CakeStackReseat

/-!
# Parity test for the CakeML stack-register reseat

Checks that the reseating of the port's hardware-numbered backend roles to
CakeML stack numbers is inverted by `riscv_names` (so applying the map once at
the Lab boundary preserves the port's existing hardware assignment) and that
the corrections for the zero and link registers match the original CakeML
convention: zero `0` becomes stack `27`, link `1` becomes stack `0`.
-/

namespace Flapjack.Test.CakeStackReseatParity

open Flapjack.RiscV

/-- Smoke check: the port's zero role reseats to the CakeML zero register. -/
example : portToStack portZeroRegister = 27 := rfl

/-- Smoke check: the port's link role reseats to the CakeML link register. -/
example : portToStack portLinkRegister = 0 := rfl

#guard portToStack portAddressScratch == 12
#guard portToStack portSpecialScratch == 11
#guard portToStack portCarryScratch == 10
#guard riscvRegisterName (portToStack portAddressScratch) == portAddressScratch
#guard riscvRegisterName (portToStack portSpecialScratch) == portSpecialScratch
#guard riscvRegisterName (portToStack portCarryScratch) == portCarryScratch
#guard riscvRegisterName (portToStack portZeroRegister) == portZeroRegister
#guard riscvRegisterName (portToStack portLinkRegister) == portLinkRegister

def removeConfig : Flapjack.StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

#guard (reseatStackRemoveConfig removeConfig).storeBase == 1
#guard (reseatStackRemoveConfig removeConfig).currHeap == 3
#guard (reseatStackRemoveConfig removeConfig).addressScratch == 12
#guard (reseatStackRemoveConfig removeConfig).scratch == 31
#guard (reseatStackRemoveConfig removeConfig).stackPointer == 20
#guard riscvRegisterName (reseatStackRemoveConfig removeConfig).storeBase == 10
#guard riscvRegisterName (reseatStackRemoveConfig removeConfig).currHeap == 12
#guard riscvRegisterName (reseatStackRemoveConfig removeConfig).addressScratch == 29

/-! `stack_remove` does not use the legacy `currHeap` field: its source
    convention is the register immediately above the stack/store-base pair,
    `k + 2`. -/
#guard (cakeStackRemoveConfig removeConfig).storeBase == 21
#guard (cakeStackRemoveConfig removeConfig).currHeap == 22

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("port zero role reseats to CakeML zero register 27",
        portToStack portZeroRegister == 27),
      ("port link role reseats to CakeML link register 0",
        portToStack portLinkRegister == 0),
      ("address scratch reseat inverts through riscv_names",
        riscvRegisterName (portToStack portAddressScratch) == portAddressScratch),
      ("special scratch reseat inverts through riscv_names",
        riscvRegisterName (portToStack portSpecialScratch) == portSpecialScratch),
      ("carry scratch reseat inverts through riscv_names",
        riscvRegisterName (portToStack portCarryScratch) == portCarryScratch),
      ("reseated scratch roles are pairwise distinct",
        portToStack portAddressScratch != portToStack portSpecialScratch &&
          portToStack portAddressScratch != portToStack portCarryScratch &&
          portToStack portSpecialScratch != portToStack portCarryScratch),
      ("stack-remove store base reseats to CakeML stack register 1",
        (reseatStackRemoveConfig removeConfig).storeBase == 1),
      ("stack-remove current heap reseats to CakeML stack register 3",
        (reseatStackRemoveConfig removeConfig).currHeap == 3),
      ("stack-remove address scratch reseats to CakeML stack register 12",
        (reseatStackRemoveConfig removeConfig).addressScratch == 12),
      ("reseated stack-remove roles invert through riscv_names",
        riscvRegisterName (reseatStackRemoveConfig removeConfig).storeBase == 10 &&
          riscvRegisterName (reseatStackRemoveConfig removeConfig).currHeap == 12 &&
          riscvRegisterName (reseatStackRemoveConfig removeConfig).addressScratch == 29),
      ("Cake stack-remove current heap is stack pointer plus two",
        (cakeStackRemoveConfig removeConfig).currHeap ==
          removeConfig.stackPointer + 2),
      ("Cake stack-remove store base is stack pointer plus one",
        (cakeStackRemoveConfig removeConfig).storeBase ==
          removeConfig.stackPointer + 1) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeStackReseatParity
