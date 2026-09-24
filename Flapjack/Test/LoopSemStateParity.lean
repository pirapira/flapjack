import Flapjack.Pancake.Semantics.LoopSemState

/-!
# Exact `loopSem$state` carrier parity

Checks the exact width-indexed `LoopSemState` against the direct HOL oracle
`loop_sem_state_carrier_probe` (num_map locals/code, total memory, set-valued
domain, clock, be) and exercises the observational bridge to the production
`LoopMachineState` including `get_var_imm` register/immediate reads.
-/

namespace Flapjack.Test.LoopSemStateParity

open Flapjack

private abbrev W := BitVec 8

/-- Sample exact carrier mirroring the HOL probe's `s1`. -/
private def exactState : LoopSemState 8 Unit :=
  { locals := fun name => if name = 0 then some (.word (BitVec.ofNat 8 7)) else none
  , globals := fun _ => none
  , memory := fun _ => .word (BitVec.ofNat 8 0)
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := 5
  , code := fun _ => none
  , be := false
  , ffi := trivialFfiState Unit ()
  , baseAddr := 0
  , topAddr := 0 }

/-- Production state satisfying the bridge for `exactState`. -/
private def machineState : LoopMachineState W Unit :=
  { locals := fun name => (exactState.locals name).map loopValueOfWordLocW
  , globals := fun global => (exactState.globals global).map loopValueOfWordLocW
  , memory := fun address => some (loopValueOfWordLocW (exactState.memory address))
  , mdomain := exactState.mdomain
  , shMdomain := exactState.shMdomain
  , clock := exactState.clock
  , code := []
  , be := exactState.be
  , ffi := exactState.ffi
  , baseAddr := exactState.baseAddr
  , topAddr := exactState.topAddr }

/-- The exact carrier's memory is total, so every production cell is present. -/
example : machineState.memory (3 : W) = some (.word (BitVec.ofNat 8 0)) := rfl

/-- Rows matching the HOL oracle. -/
example : exactState.locals 0 = some (.word (BitVec.ofNat 8 7)) := rfl
example : exactState.locals 1 = none := rfl
example : exactState.memory (3 : W) = .word (BitVec.ofNat 8 0) := rfl
example : exactState.mdomain (3 : W) = false := rfl
example : exactState.clock = 5 := rfl
example : exactState.code 0 = none := rfl
example : exactState.be = false := rfl

theorem bridgeSample : LoopMachineStateRel exactState machineState := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro name
    simp [machineState]
  · intro global
    simp [machineState]
  · intro address
    simp [machineState]
  · intro entry hmem
    simp [machineState] at hmem

/-- Register read through the bridge. -/
example : getVarImm machineState (.reg 0) = some (.word (BitVec.ofNat 8 7)) := by
  rw [getVarImm_reg_eq_of_loopMachineStateRel bridgeSample 0]
  rfl

/-- Immediate read through the bridge. -/
example : getVarImm machineState (.imm (BitVec.ofNat 8 9)) =
    some (.word (BitVec.ofNat 8 9)) :=
  getVarImm_imm_eq_of_loopMachineStateRel bridgeSample (BitVec.ofNat 8 9)

private def bridgeGuard : Bool :=
  (getVarImm machineState (.reg 0) == some (.word (BitVec.ofNat 8 7))) &&
    (getVarImm machineState (.imm (BitVec.ofNat 8 9)) ==
      some (.word (BitVec.ofNat 8 9))) &&
    (machineState.memory (3 : W) == some (.word (BitVec.ofNat 8 0)))

#guard bridgeGuard

def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS loopSem exact state carrier fields and production state bridge"
  else
    IO.println "FAIL loopSem exact state carrier bridge"
  pure bridgeGuard

end Flapjack.Test.LoopSemStateParity