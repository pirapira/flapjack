import Flapjack.Pancake.Semantics.PanSemStateEval

/-! Direct HOL oracle parity for the exact panSem `mem_store`/`mem_stores`
    ports.  The tagged definitions `panMemStoreHOL` (`mem_store_def`) and
    `panMemStoresHOL` (`mem_stores_def`) live in
    `Flapjack/Pancake/Semantics/PanSemStateEval.lean`; this module pins them to
    the direct HOL `EVAL` rows in
    `scripts/hol-probes/pan_sem_mem_store_probe.out`. -/

namespace Flapjack.Test.PanSemMemStoreHOLParity

open Flapjack

private abbrev W := RiscV.Word 64

private abbrev zeroMemory : W → HolWordLab 64 := fun _ => .word 0

private abbrev domain : W → Prop := fun address => address = 0 ∨ address = 8

private abbrev domainOnly0 : W → Prop := fun address => address = 0

private abbrev storeLookup (address : W) (value : HolWordLab 64) (cell : W) :
    Option (HolWordLab 64) :=
  (panMemStoreHOL address value domain zeroMemory).map (fun memory => memory cell)

private abbrev storesLookup (address : W) (values : List (HolWordLab 64)) (cell : W) :
    Option (HolWordLab 64) :=
  (panMemStoresHOL address values domain zeroMemory).map (fun memory => memory cell)

private abbrev storesPair (address : W) (values : List (HolWordLab 64))
    (cell₁ cell₂ : W) : Option (HolWordLab 64 × HolWordLab 64) :=
  (panMemStoresHOL address values domain zeroMemory).map
    (fun memory => (memory cell₁, memory cell₂))

/-- HOL row `ms_hit_lookup`. -/
example : storeLookup 0 (.word 7) 0 = some (.word 7) := by
  simp only [storeLookup, panMemStoreHOL, domain, zeroMemory] <;> decide

/-- HOL row `ms_hit_other`. -/
example : storeLookup 0 (.word 7) 4 = some (.word 0) := by
  simp only [storeLookup, panMemStoreHOL, domain, zeroMemory] <;> decide

/-- HOL row `ms_miss`. -/
example : (panMemStoreHOL 9 (.word 7) domain zeroMemory).isNone := by
  simp only [panMemStoreHOL, domain, zeroMemory] <;> decide

/-- HOL row `mss_two` (stride `panBytesInWord 64 = 8`). -/
example : storesPair 0 [.word 1, .word 2] 0 8 = some (.word 1, .word 2) := by
  simp only [storesPair, panMemStoresHOL, panMemStoreHOL, panBytesInWord, domain,
    zeroMemory] <;> decide

/-- HOL row `mss_empty_lookup`. -/
example : storesLookup 0 [] 3 = some (.word 0) := by
  simp only [storesLookup, panMemStoresHOL] <;> decide

/-- HOL row `mss_second_miss` (second store out of domain). -/
example : (panMemStoresHOL 0 [.word 1, .word 2] domainOnly0 zeroMemory).isNone := by
  simp only [panMemStoresHOL, panMemStoreHOL, panBytesInWord, domainOnly0,
    zeroMemory] <;> decide

private def memStoreGuard : Bool :=
  (storeLookup 0 (.word 7) 0 == some (.word 7)) &&
  (storeLookup 0 (.word 7) 4 == some (.word 0)) &&
  (panMemStoreHOL 9 (.word 7) domain zeroMemory).isNone &&
  (storesPair 0 [.word 1, .word 2] 0 8 == some (.word 1, .word 2)) &&
  (storesLookup 0 [] 3 == some (.word 0)) &&
  (panMemStoresHOL 0 [.word 1, .word 2] domainOnly0 zeroMemory).isNone

#eval memStoreGuard
#guard memStoreGuard

def runChecks : IO Bool := do
  if memStoreGuard then
    IO.println "PASS panSem mem_store/mem_stores exact carriers match all 6 oracle rows"
  else
    IO.println "FAIL panSem mem_store/mem_stores exact carriers"
  pure memStoreGuard

end Flapjack.Test.PanSemMemStoreHOLParity