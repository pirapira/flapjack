import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-! Direct original HOL observations for the restricted total Crep Store clause
   are recorded by `crep_store_eval_probeScript.sml`. -/

namespace Flapjack.Test.CrepSemTotalStoreParity

open Flapjack

def sampleState : CrepHolState (BitVec 64) Unit :=
  { locals := fun name => if name == 0 then some (.word 7) else none
    globals := fun _ => none
    code := fun _ => none
    memory := fun address => .word (BitVec.ofNat 64 (address.toNat + 1))
    memaddrs := fun address => address == 10
    shMemaddrs := fun _ => false
    clock := 5
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

def storeOracleRowsMatch : Bool :=
  let state := sampleState
  let address := BitVec.ofNat 64 10
  let otherAddress := BitVec.ofNat 64 11
  let success := match evalCrepClockProg (.store (.const address) (.const 9)) state with
    | (none, post) => post.memory address == .word 9 &&
        post.memory otherAddress == state.memory otherAddress &&
        post.locals 0 == state.locals 0 && post.clock == state.clock &&
        post.globals 0 == state.globals 0 && post.baseAddress == state.baseAddress &&
        post.topAddress == state.topAddress
    | _ => false
  let addressError := match evalCrepClockProg (.store (.var 9) (.const 9)) state with
    | (some .error, post) => post.memory address == state.memory address &&
        post.clock == state.clock && post.locals 0 == state.locals 0
    | _ => false
  let valueError := match evalCrepClockProg (.store (.const address) (.var 9)) state with
    | (some .error, post) => post.memory address == state.memory address &&
        post.clock == state.clock && post.locals 0 == state.locals 0
    | _ => false
  let domainError := match evalCrepClockProg
      (.store (.const otherAddress) (.const 9)) state with
    | (some .error, post) => post.memory address == state.memory address &&
        post.memory otherAddress == state.memory otherAddress &&
        post.clock == state.clock && post.locals 0 == state.locals 0
    | _ => false
  success && addressError && valueError && domainError

#guard storeOracleRowsMatch

theorem storeSuccessMatchesHolMemStore
    (state : CrepHolState (BitVec 64) Unit)
    (address value : BitVec 64)
    (hdomain : state.memaddrs address = true) :
    evalCrepClockProg (.store (.const address) (.const value)) state =
      (none, { state with memory := fun current =>
        if current = address then .word value else state.memory current }) := by
  apply evalCrepClockProg_store_success
  · simp [evalCrepHolExp]
  · simp [evalCrepHolExp]
  · exact hdomain

def runChecks : IO Bool := do
  if storeOracleRowsMatch then
    IO.println "PASS total Crep HOL Store success/address/value/domain clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Store success/address/value/domain clauses match direct oracle"
  pure storeOracleRowsMatch

end Flapjack.Test.CrepSemTotalStoreParity
