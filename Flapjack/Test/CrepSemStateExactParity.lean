import Flapjack.Pancake.Semantics.CrepSem.StateExact

/-!
Direct HOL-row fixtures for the finite-support-carrier CrepSem state helpers.
Reproduces `scripts/hol-probes/crep_dec_clock_simp_probe.out`,
`scripts/hol-probes/crep_fix_clock_probe.out`, and
`scripts/hol-probes/crep_mem_load_probe.out` (flapjack-pxn.18.3.7.1.3.1.1.3.1).
-/

namespace Flapjack.Test.CrepSemStateExactParity

open Flapjack.Basis.Pure.MlString

private abbrev Word8 := BitVec 8

private def emptyLocals : HolFiniteMapExact Nat (HolWordLab 8) where
  lookup := fun _ => none
  finiteSupport := ⟨[], by intro key h; simp at h⟩

private def emptyGlobals : HolFiniteMapExact (BitVec 5) (HolWordLab 8) where
  lookup := fun _ => none
  finiteSupport := ⟨[], by intro key h; simp at h⟩

private def emptyCode : HolFiniteMapExact MlString (List Nat × CrepProgHOL 8) where
  lookup := fun _ => none
  finiteSupport := ⟨[], by intro key h; simp at h⟩

private def localsWithOne : HolFiniteMapExact Nat (HolWordLab 8) where
  lookup := fun name => if name = 1 then some (.word 7) else none
  finiteSupport := by
    refine ⟨[1], ?_⟩
    intro name hlookup
    by_cases h : name = 1
    · simp [h]
    · simp [h] at hlookup

private def dummyFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    ffiState := ()
    ioEvents := [] }

/-- The clock-5 fixture mirroring the HOL `dec_clock_simp_probe` state. -/
abbrev baseState : CrepSemHOLState 8 Unit where
  locals := emptyLocals
  globals := emptyGlobals
  code := emptyCode
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := dummyFfi
  baseAddr := 0
  topAddr := 100

abbrev memState : CrepSemHOLState 8 Unit where
  locals := emptyLocals
  globals := emptyGlobals
  code := emptyCode
  memory := fun _ => .word 7
  memaddrs := fun address => address = 0
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := dummyFfi
  baseAddr := 0
  topAddr := 100

abbrev memStateWide : CrepSemHOLState 8 Unit where
  locals := emptyLocals
  globals := emptyGlobals
  code := emptyCode
  memory := fun _ => .word 7
  memaddrs := fun address => address = 0 ∨ address = 2
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := dummyFfi
  baseAddr := 0
  topAddr := 100

abbrev withLocalsOne (clock : Nat) : CrepSemHOLState 8 Unit where
  locals := localsWithOne
  globals := emptyGlobals
  code := emptyCode
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := clock
  be := false
  ffi := dummyFfi
  baseAddr := 0
  topAddr := 100

def decClockGuard : Bool :=
  (decClockCrepSemHOL baseState).clock == 4 &&
    ((decClockCrepSemHOL baseState).globals.lookup 0 == baseState.globals.lookup 0) &&
    ((decClockCrepSemHOL baseState).be == false) &&
    (decide ((decClockCrepSemHOL baseState).topAddr = (100 : Word8)))

def fixClockClampsGuard : Bool :=
  let step : Option Nat × CrepSemHOLState 8 Unit :=
    (some 7, withLocalsOne 9)
  ((fixClockCrepSemHOL (withLocalsOne 5) step).2.clock == 5) &&
    ((fixClockCrepSemHOL (withLocalsOne 5) step).2.locals.lookup 1 == some (.word 7))

def fixClockKeepsLowerGuard : Bool :=
  let step : Option Nat × CrepSemHOLState 8 Unit :=
    (some 7, withLocalsOne 3)
  ((fixClockCrepSemHOL (withLocalsOne 5) step).2.clock == 3) &&
    ((fixClockCrepSemHOL (withLocalsOne 5) step).2.locals.lookup 1 == some (.word 7))

def memLoadGuard : Bool :=
  (memLoadCrepSemHOL (0 : Word8) memState == some (.word 7)) &&
    (memLoadCrepSemHOL (1 : Word8) memState).isNone &&
    (memLoadCrepSemHOL (0 : Word8) memStateWide == some (.word 7))

def stateExactGuard : Bool :=
  decClockGuard && fixClockClampsGuard && fixClockKeepsLowerGuard && memLoadGuard

#eval decClockGuard
#eval fixClockClampsGuard
#eval fixClockKeepsLowerGuard
#eval memLoadGuard
#eval stateExactGuard

#guard decClockGuard
#guard fixClockClampsGuard
#guard fixClockKeepsLowerGuard
#guard memLoadGuard
#guard stateExactGuard

example :
    ((fixClockCrepSemHOL (withLocalsOne 5) (some 7, withLocalsOne 9)).2).clock = 5 := rfl

example (res : Option Nat) (s1 : CrepSemHOLState 8 Unit)
    (h : fixClockCrepSemHOL (withLocalsOne 5) (some 7, withLocalsOne 9) = (res, s1)) :
    s1.clock ≤ 5 :=
  fixClockCrepSemHOL_IMP_LESS_EQ (withLocalsOne 5) (some 7, withLocalsOne 9) res s1 h

def runChecks : IO Bool := do
  if stateExactGuard then
    IO.println "PASS exact crepSem dec_clock/fix_clock/mem_load over the finite-support carrier"
    pure true
  else
    IO.println "FAIL exact crepSem dec_clock/fix_clock/mem_load over the finite-support carrier"
    pure false

end Flapjack.Test.CrepSemStateExactParity
