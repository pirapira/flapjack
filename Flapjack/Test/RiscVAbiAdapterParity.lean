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

The source adapter `Flapjack.wordRiscVAbiSourceRegister` gives the hardware
register of an even Word name `2r`, i.e. `riscv_names r`.  Cake applies the map
to every Lab register, so the adapter must do so for every even name, not only
`r` in `{0,1,2,3,4}`.  A restricted adapter makes `2` and `10` collide on
hardware register `10` (and `6` with `12` on `12`); the guest reproducer
(GH#1015 `guest.pp.pnk`, renamed `main` section) then fails allocation with
`wordAllocateVarsWithFixedLocations = none` on the fixed-only conflicting edges
`(2,10)` and `(6,12)`.  The guards below check the full map, including that the
fixed sources stay injective.
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

/-- `wordRiscVAbiSourceRegister 2r` is `riscv_names r` for every even source
    name, i.e. for every name the fixed-source path can contain. -/
def adapterMatchesOracleOnEvenNames : Bool :=
  (List.range 64).all (fun source =>
    source % 2 != 0 ||
      wordRiscVAbiSourceRegister source == riscvRegisterName (source / 2))

#guard adapterMatchesOracleOnEvenNames

/-- The adapter keeps the fixed even sources injective, so the clash tree of a
    section can always be satisfied by the fixed locations. -/
def adapterInjectiveOnFixedEvenNames : Bool :=
  let images :=
    ((List.range 32).filter (fun source => source % 2 == 0)).map
      wordRiscVAbiSourceRegister
  images.eraseDups.length == images.length

#guard adapterInjectiveOnFixedEvenNames

/-- The two guest edges that previously collapsed now stay distinct. -/
def adapterKeepsGuestEdgesDistinct : Bool :=
  wordRiscVAbiSourceRegister 2 != wordRiscVAbiSourceRegister 10 &&
    wordRiscVAbiSourceRegister 6 != wordRiscVAbiSourceRegister 12

#guard adapterKeepsGuestEdgesDistinct

/-- The minimized fixed-source allocator witness now succeeds for both guest
    clash edges once the full `riscv_names` adapter is applied. -/
def adapterAllocatesGuestEdges : Bool :=
  (wordAllocateVarsWithFixedLocations [2, 10] [(2, 10)] []
      (wordRiscVFixedSourceLocations [2, 10])).isSome &&
    (wordAllocateVarsWithFixedLocations [6, 12] [(6, 12)] []
      (wordRiscVFixedSourceLocations [6, 12])).isSome

#guard adapterAllocatesGuestEdges

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [("the ported register map matches the riscv_names HOL oracle",
        mapMatchesOracle),
      ("registers outside the oracle stay identity like Cake",
        mapIdentityOutsideOracle),
      ("the ABI adapter maps every even Word name through riscv_names",
        adapterMatchesOracleOnEvenNames),
      ("the ABI adapter keeps the fixed even sources injective",
        adapterInjectiveOnFixedEvenNames),
      ("the ABI adapter keeps the guest clash edges distinct",
        adapterKeepsGuestEdgesDistinct),
      ("the minimized guest fixed-source allocation succeeds",
        adapterAllocatesGuestEdges)]
  let mut ok := true
  for check in checks do
    if check.2 then
      IO.println s!"PASS {check.1}"
    else
      ok := false
      IO.println s!"FAIL {check.1}"
  return ok

end Flapjack.Test.RiscVAbiAdapterParity
