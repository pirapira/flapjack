import Flapjack.Pancake.Semantics.PanSem.MemStore32Alt

/-!
# Parity for the exact `panSem$mem_store_32_alt` OR/shift assembly

Replays the direct original-HOL rows in
`scripts/hol-probes/pan_sem_mem_store_32_probe.out`:
`ms32_aligned = Word 0x11223344w`, `ms32_aligned4 = Word 0x1122334400000000w`,
`ms32_unaligned = Word 0w`, `ms32_outside_domain = Word 0w`,
`ms32_bigendian = Word 0x1122334400000000w`, `ms32_other_cell = Word 0w`
(each probing the memory cell after the store).
-/

namespace Flapjack.Test.PanSemMemStore32AltParity

open Flapjack

private abbrev Word64 := RiscV.Word 64

def memory64 : Word64 → HolWordLab 64 := fun _ => .word 0

abbrev domain64 : Word64 → Prop := fun address => address = 0

def value32 : RiscV.Word 32 := BitVec.ofNat 32 0x11223344

def wordNat (lab : HolWordLab 64) : Nat :=
  match lab with
  | .word value => value.toNat

def projected (memory : Option (Word64 → HolWordLab 64)) (address : Word64) : Option Nat :=
  memory.map (fun stored => wordNat (stored address))

def alignedGuard : Bool :=
  projected (panMemStore32HOL memory64 domain64 false 0 value32) 0 == some 0x11223344

def aligned4Guard : Bool :=
  projected (panMemStore32HOL memory64 domain64 false 4 value32) 0 == some 0x1122334400000000

def unalignedGuard : Bool := (panMemStore32HOL memory64 domain64 false 2 value32).isNone

def outsideDomainGuard : Bool :=
  (panMemStore32HOL memory64 (fun _ => False) false 0 value32).isNone

def bigEndianGuard : Bool :=
  projected (panMemStore32HOL memory64 domain64 true 0 value32) 0 == some 0x1122334400000000

def otherCellGuard : Bool :=
  projected (panMemStore32HOL memory64 domain64 false 0 value32) 8 == some 0

def altLittleGuard : Bool := store32Alt 0 false value32 0 == BitVec.ofNat 64 0x11223344

def altBigGuard : Bool := store32Alt 0 true value32 0 == BitVec.ofNat 64 0x1122334400000000

example : True := by
  have _ := panMemStore32HOL_eq_alt memory64 domain64 false 0 value32
  have _ := panMemStore32HOL_eq_alt memory64 domain64 true 0 value32
  have _ := panMemStore32HOL_eq_alt
    (fun _ : RiscV.Word 1 => HolWordLab.word (BitVec.ofNat 1 0))
    (fun _ => True) false (BitVec.ofNat 1 0) value32
  have _ := panMemStore32HOL_eq_alt
    (fun _ : RiscV.Word 7 => HolWordLab.word (BitVec.ofNat 7 0))
    (fun _ => True) true (BitVec.ofNat 7 0) value32
  have _ := panMemStore32HOL_eq_alt
    (fun _ : RiscV.Word 24 => HolWordLab.word (BitVec.ofNat 24 0))
    (fun _ => True) false (BitVec.ofNat 24 0) value32
  trivial

#guard alignedGuard
#guard aligned4Guard
#guard unalignedGuard
#guard outsideDomainGuard
#guard bigEndianGuard
#guard otherCellGuard
#guard altLittleGuard
#guard altBigGuard

def memStore32AltGuard : Bool :=
  alignedGuard && aligned4Guard && unalignedGuard && outsideDomainGuard &&
    bigEndianGuard && otherCellGuard && altLittleGuard && altBigGuard

#eval memStore32AltGuard
#guard memStore32AltGuard

def runChecks : IO Bool := do
  if memStore32AltGuard then
    IO.println "PASS exact panSem mem_store_32_alt OR/shift assembly (8 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem mem_store_32_alt OR/shift assembly"
    pure false

end Flapjack.Test.PanSemMemStore32AltParity
