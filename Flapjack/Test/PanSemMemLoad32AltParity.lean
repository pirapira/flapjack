import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt

/-!
# Parity for the exact `panSem$mem_load_32_alt` OR/shift assembly

Replays the direct original-HOL rows in
`scripts/hol-probes/pan_sem_state_eval_probe.out`:
`mem_load_32_def_little = SOME 0x55667788w`,
`mem_load_32_def_big = SOME 0x11223344w`,
`mem_load_32_def_misaligned = NONE`,
`mem_load_32_def_missing = NONE`, and the width-24 row
`mem_load_32_def_w24_addr4 = SOME 0x22331122w`.
-/

namespace Flapjack.Test.PanSemMemLoad32AltParity

open Flapjack

private abbrev Word64 := RiscV.Word 64

def memory64 : Word64 → HolWordLab 64 :=
  fun address => if address = 0 then .word (BitVec.ofNat 64 0x1122334455667788) else .word 0

abbrev domain64 : Word64 → Prop := fun address => address = 0

def projected (result : Option (RiscV.Word 32)) : Option Nat := result.map (fun word => word.toNat)

def littleGuard : Bool := projected (panMemLoad32HOL memory64 domain64 false 0) == some 0x55667788

def bigGuard : Bool := projected (panMemLoad32HOL memory64 domain64 true 0) == some 0x11223344

def misalignedGuard : Bool := (panMemLoad32HOL memory64 domain64 false 1).isNone

def missingGuard : Bool := (panMemLoad32HOL memory64 (fun _ => False) false 0).isNone

private abbrev Word24 := RiscV.Word 24

def memory24 : Word24 → HolWordLab 24 :=
  fun address => if address = 4 then .word (BitVec.ofNat 24 0x112233) else .word 0

abbrev domain24 : Word24 → Prop := fun address => address = 4

def width24Guard : Bool := projected (panMemLoad32HOL memory24 domain24 false 4) == some 0x22331122

example : True := by
  have _ := panMemLoad32HOL_eq_alt memory64 domain64 false 0
  have _ := panMemLoad32HOL_eq_alt memory64 domain64 true 0
  have _ := panMemLoad32HOL_eq_alt
    (fun _ : RiscV.Word 1 => HolWordLab.word (BitVec.ofNat 1 0))
    (fun _ => True) false (BitVec.ofNat 1 0)
  have _ := panMemLoad32HOL_eq_alt
    (fun _ : RiscV.Word 4 => HolWordLab.word (BitVec.ofNat 4 11))
    (fun _ => True) true (BitVec.ofNat 4 0)
  have _ := panMemLoad32HOL_eq_alt memory24 domain24 false 4
  trivial

#guard littleGuard
#guard bigGuard
#guard misalignedGuard
#guard missingGuard
#guard width24Guard

def memLoad32AltGuard : Bool :=
  littleGuard && bigGuard && misalignedGuard && missingGuard && width24Guard

#eval memLoad32AltGuard
#guard memLoad32AltGuard

def runChecks : IO Bool := do
  if memLoad32AltGuard then
    IO.println "PASS exact panSem mem_load_32_alt OR/shift assembly (5 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem mem_load_32_alt OR/shift assembly"
    pure false

end Flapjack.Test.PanSemMemLoad32AltParity
