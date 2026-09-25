import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Exact HOL `mem_store_32` parity

Executable checks for the exact port `panMemStore32HOL`
(`cakeml/pancake/semantics/panSemScript.sml:327-346`) against the direct HOL
oracle `scripts/hol-probes/pan_sem_mem_store_32_probe.out` (6 rows).

The probe fixes a 64-bit word with memory `fun _ => .word 0` and domain `{0}`,
stores the `word32` value `0x11223344`, and observes the resulting aligned cell
(little/big endian), the unaligned and out-of-domain `NONE` cases, and an
untouched other cell.
-/
namespace Flapjack.Test.PanSemMemStore32HOLParity

open Flapjack

private abbrev W := RiscV.Word 64

private def zeroMemory : W → HolWordLab 64 := fun _ => .word 0

/-- `abbrev` so instance search can unfold it when synthesizing
    `DecidablePred domainAt0`. -/
private abbrev domainAt0 : W → Prop := fun address => address = 0

/-- Project the stored cell out of the option memory so the result is
    decidable (the function type itself has no `DecidableEq`). -/
private abbrev storedCellAt (bigEndian : Bool) (address : W) (value : RiscV.Word 32)
    (cell : W) : Option (HolWordLab 64) :=
  (panMemStore32HOL zeroMemory domainAt0 bigEndian address value).map
    (fun memory => memory cell)

/-- Oracle row `ms32_aligned`. -/
example : storedCellAt false 0 (BitVec.ofNat 32 0x11223344) 0 =
    some (.word (BitVec.ofNat 64 0x11223344)) := by
  simp only [storedCellAt, panMemStore32HOL, panByteAlignHOL, panGetByteHOL,
    panSetByteHOL, zeroMemory, domainAt0] <;> decide

/-- Oracle row `ms32_aligned4`. -/
example : storedCellAt false 4 (BitVec.ofNat 32 0x11223344) 0 =
    some (.word (BitVec.ofNat 64 0x1122334400000000)) := by
  simp only [storedCellAt, panMemStore32HOL, panByteAlignHOL, panGetByteHOL,
    panSetByteHOL, zeroMemory, domainAt0] <;> decide

/-- Oracle row `ms32_unaligned`. -/
example : storedCellAt false 2 (BitVec.ofNat 32 0x11223344) 0 = none := by
  simp only [storedCellAt, panMemStore32HOL, panByteAlignHOL, panGetByteHOL,
    panSetByteHOL, zeroMemory, domainAt0] <;> decide

/-- Oracle row `ms32_bigendian`. -/
example : storedCellAt true 0 (BitVec.ofNat 32 0x11223344) 0 =
    some (.word (BitVec.ofNat 64 0x1122334400000000)) := by
  simp only [storedCellAt, panMemStore32HOL, panByteAlignHOL, panGetByteHOL,
    panSetByteHOL, zeroMemory, domainAt0] <;> decide

/-- Oracle row `ms32_other_cell`: the untouched cell is preserved. -/
example : storedCellAt false 0 (BitVec.ofNat 32 0x11223344) 8 = some (.word 0) := by
  simp only [storedCellAt, panMemStore32HOL, panByteAlignHOL, panGetByteHOL,
    panSetByteHOL, zeroMemory, domainAt0] <;> decide

/-- Oracle row `ms32_outside_domain`: an empty domain yields `none`. -/
example : (panMemStore32HOL zeroMemory (fun _ => False) false 0
      (BitVec.ofNat 32 0x11223344)).map (fun memory => memory 0) = none := by
  simp only [panMemStore32HOL, panByteAlignHOL, panGetByteHOL, panSetByteHOL,
    zeroMemory] <;> decide

/-- Boolean mirror of the six oracle rows. -/
private def memStore32Guard : Bool :=
  (storedCellAt false 0 (BitVec.ofNat 32 0x11223344) 0 ==
      some (.word (BitVec.ofNat 64 0x11223344))) &&
    (storedCellAt false 4 (BitVec.ofNat 32 0x11223344) 0 ==
      some (.word (BitVec.ofNat 64 0x1122334400000000))) &&
    (storedCellAt false 2 (BitVec.ofNat 32 0x11223344) 0).isNone &&
    (storedCellAt true 0 (BitVec.ofNat 32 0x11223344) 0 ==
      some (.word (BitVec.ofNat 64 0x1122334400000000))) &&
    (storedCellAt false 0 (BitVec.ofNat 32 0x11223344) 8 == some (.word 0)) &&
    ((panMemStore32HOL zeroMemory (fun _ => False) false 0
        (BitVec.ofNat 32 0x11223344)).map (fun memory => memory 0)).isNone

#eval memStore32Guard
#guard memStore32Guard

def runChecks : IO Bool := do
  if memStore32Guard then
    IO.println "PASS panSem mem_store_32 exact carrier matches all 6 oracle rows"
    pure true
  else
    IO.println "FAIL panSem mem_store_32 exact carrier"
    pure false

end Flapjack.Test.PanSemMemStore32HOLParity