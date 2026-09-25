import Flapjack.Pancake.Semantics.PanSem.ShMemExact

/-!
# Parity for exact HOL `sh_mem_load` / `sh_mem_store`

Reproduces `scripts/hol-probes/pan_sem_sh_mem_probe.out` (8 rows): the `nb = 0`
in/out-of-`sh_memaddrs` branches, the byte-aligned `nb = 1` branch, the
`FFI_final`-clears-locals branch, and the `FFI_return` event/ffi update for both
the load and store primitives. `PanSemResultExact`/`ValueHOL` have no
`DecidableEq`, so the assertions use structural `Bool` matchers.
-/

namespace Flapjack.Test.PanSemShMemHOLParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS)

private abbrev W := RiscV.Word 64

private def ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

/-- Oracle returning a same-length zero byte list, so `callFFIHOL` returns. -/
private def okOracle : HolOracle Unit :=
  fun _ _ _ bytes => .ret () (List.replicate bytes.length (w8 0))

private def finalOracle : HolOracle Unit := fun _ _ _ _ => .final .failed

private def okFfi : HolFfiState Unit :=
  { oracle := okOracle, ffiState := (), ioEvents := [] }

private def finalFfi : HolFfiState Unit :=
  { oracle := finalOracle, ffiState := (), ioEvents := [] }

private abbrev mkState (domain : W → Prop) (ffi : HolFfiState Unit) :
    PanSemStateExact 64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := domain
    clock := 5
    be := false
    ffi := ffi
    baseAddr := 0
    topAddr := 0 }

private abbrev hitState : PanSemStateExact 64 Unit := mkState (fun a => a = 0) okFfi
private abbrev missState : PanSemStateExact 64 Unit := mkState (fun a => a = 1) okFfi
private abbrev alignState : PanSemStateExact 64 Unit := mkState (fun a => a = 8) okFfi
private abbrev finalState : PanSemStateExact 64 Unit := mkState (fun a => a = 0) finalFfi

private def loadHit := shMemLoadHOLExact hitState .local (ml "x") 0 0
private def loadMiss := shMemLoadHOLExact missState .local (ml "x") 0 0
private def loadAligned := shMemLoadHOLExact alignState .local (ml "x") 8 1
private def loadFinal := shMemLoadHOLExact finalState .local (ml "x") 0 0
private def storeHit := shMemStoreHOLExact hitState 7 0 0
private def storeMiss := shMemStoreHOLExact missState 7 0 0
private def storeFinal := shMemStoreHOLExact finalState 7 0 0

private def isErrorResult : Option (PanSemResultExact 64) → Bool
  | some .error => true
  | _ => false

private def isWordZero : Option (ValueHOL 64) → Bool
  | some (.val (.word w)) => w == 0
  | _ => false

/-- Rows 1-8 of the direct HOL oracle. -/
private def shMemGuard : Bool :=
  isWordZero (loadHit.2.locals (ml "x")) &&
  (loadHit.2.ffi.ioEvents.length == 1) &&
  isErrorResult loadMiss.1 &&
  isWordZero (loadAligned.2.locals (ml "x")) &&
  (loadFinal.2.locals (ml "x")).isNone &&
  (storeHit.2.ffi.ioEvents.length == 1) &&
  isErrorResult storeMiss.1 &&
  (storeFinal.2.ffi.ioEvents.length == 0)

example : isWordZero (loadHit.2.locals (ml "x")) = true := by decide
example : loadHit.2.ffi.ioEvents.length = 1 := by decide
example : isErrorResult loadMiss.1 = true := by decide
example : isWordZero (loadAligned.2.locals (ml "x")) = true := by decide
example : (loadFinal.2.locals (ml "x")).isNone = true := by decide
example : storeHit.2.ffi.ioEvents.length = 1 := by decide
example : isErrorResult storeMiss.1 = true := by decide
example : storeFinal.2.ffi.ioEvents.length = 0 := by decide

#eval shMemGuard
#guard shMemGuard

def runChecks : IO Bool := do
  if shMemGuard then
    IO.println "PASS panSem sh_mem_load/sh_mem_store exact carriers match all 8 oracle rows"
  else
    IO.println "FAIL panSem sh_mem_load/sh_mem_store exact carriers"
  pure shMemGuard

end Flapjack.Test.PanSemShMemHOLParity