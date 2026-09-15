import Flapjack.RiscV.PipelineDiagnostics

/-!
# Cake register-renaming oracle for the source-facing ABI adapter

`scripts/hol-probes/riscv_names_probeScript.sml` evaluates the original
CakeML `riscv_names` map (`cakeml/compiler/backend/riscv/riscv_configScript.sml`)
directly in HOL.  The recorded answers are:

  0 -> 1, 1 -> 10, 2 -> 11, 3 -> 12, 4 -> 13,
  10 -> 27, 11 -> 28, 12 -> 29, 13 -> 30,
  27 -> 0, 28 -> 2, 29 -> 3, 30 -> 4,
  everything else unset (identity).

`Flapjack.RiscV.riscvRegisterName` is the port of that map, so the guards below
are checked against the original oracle rather than a transcription.

The source adapter `Flapjack.wordRiscVAbiSourceRegister` is supposed to give the
hardware register of an even Word name `2r`, i.e. `riscv_names r`.  It currently
does that only for `r` in `{0,1,2,3,4}` and leaves every larger even name
unchanged, which makes `2` and `10` collide on hardware register `10` (and `6`
with `12` on `12`).  The guest reproducer (GH#1015 `guest.pp.pnk`, renamed
`main` section) then fails allocation with `wordAllocateVarsWithFixedLocations =
none` on the fixed-only conflicting edges `(2,10)` and `(6,12)`.  The mismatch is
pinned as a tracked gap, not accepted.
-/

open Flapjack Flapjack.RiscV

namespace Flapjack.Test.RiscVAbiAdapterParity

/-- Oracle answers from the HOL probe for `riscv_names`. -/
def oracleAnswers : List (Nat × Nat) :=
  [(0, 1), (1, 10), (2, 11), (3, 12), (4, 13), (10, 27), (11, 28), (12, 29),
    (13, 30), (27, 0), (28, 2), (29, 3), (30, 4)]

/-- The ported map agrees with every recorded HOL oracle value. -/
def mapMatchesOracle : Bool :=
  oracleAnswers.all (fun entry => riscvRegisterName entry.1 == entry.2)

#guard mapMatchesOracle

/-- Cake leaves the registers outside the recorded map unchanged. -/
def mapIdentityOutsideOracle : Bool :=
  ([5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
      31]).all (fun register => riscvRegisterName register == register)

#guard mapIdentityOutsideOracle

/-- `wordRiscVAbiSourceRegister 2r` is `riscv_names r` exactly for the ABI
    argument registers `r = 0..4`. -/
def adapterMatchesOracleOnArguments : Bool :=
  ([0, 2, 4, 6, 8]).all (fun source =>
    wordRiscVAbiSourceRegister source == riscvRegisterName (source / 2))

#guard adapterMatchesOracleOnArguments

/-- Tracked gap: the adapter collapses the distinct abstract registers `1`
    (even name `2`) and `5` (even name `10`) onto hardware `10`, while Cake
    keeps them distinct.  Fixed sources therefore cannot satisfy the clash tree
    for the guest `main` section.  Recorded, not accepted. -/
def adapterCollidesDistinctRegisters : Bool :=
  wordRiscVAbiSourceRegister 2 == wordRiscVAbiSourceRegister 10 &&
    riscvRegisterName 1 != riscvRegisterName 5

#guard adapterCollidesDistinctRegisters

/-- The Cake-faithful target for even name `10` is hardware `5`. -/
def adapterGapTracked : Bool :=
  wordRiscVAbiSourceRegister 10 != riscvRegisterName 5

#guard adapterGapTracked

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [("the ported register map matches the riscv_names HOL oracle",
        mapMatchesOracle),
      ("registers outside the oracle stay identity like Cake",
        mapIdentityOutsideOracle),
      ("the ABI adapter matches the oracle on the argument registers",
        adapterMatchesOracleOnArguments),
      ("the ABI adapter collapse of even names 2 and 10 is tracked, not accepted",
        adapterCollidesDistinctRegisters),
      ("the ABI adapter target for even name 10 differs from the oracle",
        adapterGapTracked)]
  let mut ok := true
  for check in checks do
    if check.2 then
      IO.println s!"PASS {check.1}"
    else
      ok := false
      IO.println s!"FAIL {check.1}"
  return ok

end Flapjack.Test.RiscVAbiAdapterParity
