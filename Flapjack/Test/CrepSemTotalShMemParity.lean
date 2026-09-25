import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-! Direct original HOL rows for the restricted state-owned ShMem evaluator. -/

namespace Flapjack.Test.CrepSemTotalShMemParity

open Flapjack

def address : BitVec 64 := BitVec.ofNat 64 10

def echoOracle : FfiOracle Unit :=
  fun _ ffiState _ bytes => .returned ffiState bytes

def finalOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .diverged

def stateWith (oracle : FfiOracle Unit) (domain : BitVec 64 → Bool) :
    CrepHolState (BitVec 64) Unit :=
  { locals := fun name =>
      if name == 0 then some (.word 7)
      else if name == 1 then some (.word 0)
      else none
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := domain
    clock := 5
    bigEndian := false
    ffi := { oracle := oracle, state := (), ioEvents := [] }
    baseAddress := 0
    topAddress := 100 }

def echoPairs (bytes : List UInt8) : List (UInt8 × UInt8) :=
  bytes.map fun byte => (byte, byte)

def shmemRowsMatch : Bool := Id.run do
  let domain := fun value : BitVec 64 => value == address
  let state := stateWith echoOracle domain
  let loadOk := match evalCrepClockProg (.sharedMemory .load 1 (.const address)) state with
    | (none, post) =>
        post.locals 1 == some (.word address) &&
        post.ffi.ioEvents.length == 1 &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedRead &&
            event.configuration == [0] &&
            event.bytes == echoPairs (crepClockWordToBytes address)
        | _ => false
    | _ => false
  let storeOk := match evalCrepClockProg (.sharedMemory .store 0 (.const address)) state with
    | (none, post) =>
        post.locals 0 == some (.word 7) &&
        post.ffi.ioEvents.length == 1 &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedWrite &&
            event.configuration == [0] &&
            event.bytes == echoPairs
              (crepClockWordToBytes (BitVec.ofNat 64 7) ++ crepClockWordToBytes address)
        | _ => false
    | _ => false
  let alignedState := stateWith echoOracle
    (fun value : BitVec 64 => value == BitVec.ofNat 64 8)
  let load8Ok := match evalCrepClockProg
      (.sharedMemory .load8 1 (.const address)) alignedState with
    | (none, post) =>
        post.locals 1 == some (.word address) &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedRead &&
            event.configuration == [1] &&
            event.bytes == echoPairs (crepClockWordToBytes address)
        | _ => false
    | _ => false
  let store8Ok := match evalCrepClockProg
      (.sharedMemory .store8 0 (.const address)) alignedState with
    | (none, post) =>
        post.locals 0 == some (.word 7) &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedWrite &&
            event.configuration == [1] && event.bytes.length == 9 &&
            event.bytes == echoPairs
              ((crepClockWordToBytes (BitVec.ofNat 64 7)).take 1 ++
                crepClockWordToBytes address)
        | _ => false
    | _ => false
  let domainError := match evalCrepClockProg
      (.sharedMemory .load8 1 (.const address)) state with
    | (some .error, post) => post.locals 1 == state.locals 1 && post.ffi.ioEvents == []
    | _ => false
  let missingLocalError := match evalCrepClockProg
      (.sharedMemory .load 9 (.const address)) state with
    | (some .error, post) => post.locals 0 == state.locals 0 && post.ffi.ioEvents == []
    | _ => false
  let finalState := stateWith finalOracle domain
  let finalLoad := match evalCrepClockProg
      (.sharedMemory .load 1 (.const address)) finalState with
    | (some (.finalFfi event), post) =>
        event.outcome == .diverged && post.locals 0 == none &&
        post.ffi.ioEvents == []
    | _ => false
  pure (loadOk && storeOk && load8Ok && store8Ok && domainError &&
    missingLocalError && finalLoad)

#guard shmemRowsMatch

theorem shmemLoadDomainError
    (state : CrepHolState (BitVec 64) Unit)
    (addressExp : CrepExp (BitVec 64)) (value : BitVec 64)
    (haddress : evalCrepHolExp state addressExp = some value)
    (cell : PanWordLab (BitVec 64))
    (hdestination : state.locals 1 = some cell)
    (hdomain : state.shMemaddrs (holByteAlignBitVec value) = false) :
    evalCrepClockShMem .load8 1 addressExp state = (some .error, state) := by
  simp [evalCrepClockShMem, crepRuntimeMemWidth, haddress, hdestination, hdomain]

theorem shmemLoadExpressionError
    (state : CrepHolState (BitVec 64) Unit)
    (addressExp : CrepExp (BitVec 64))
    (haddress : evalCrepHolExp state addressExp = none) :
    evalCrepClockShMem .load 1 addressExp state = (some .error, state) := by
  simp [evalCrepClockShMem, haddress]

def runChecks : IO Bool := do
  if shmemRowsMatch then
    IO.println "PASS total Crep HOL ShMem success/domain/error/final clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL ShMem success/domain/error/final clauses match direct oracle"
  pure shmemRowsMatch

end Flapjack.Test.CrepSemTotalShMemParity
