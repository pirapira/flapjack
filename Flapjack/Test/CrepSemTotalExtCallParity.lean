import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-! Direct HOL-EVAL observations for `crepSem$evaluate_def` are recorded in
`scripts/hol-probes/crep_ext_call_eval_probe.out`. These guards exercise the
same success, final-FFI, missing-local, and failed-read rows on the restricted
RISC-V state fragment. The fragment remains untagged because its executable
String/UInt8 FFI carriers and fixed RISC-V memory model are not HOL's generic
mlstring/word8/arbitrary-word carriers. -/

namespace Flapjack.Test.CrepSemTotalExtCallParity

open Flapjack

def echoOracle : FfiOracle Unit := fun _ ffiState _ bytes =>
  .returned ffiState (bytes.map fun _ => UInt8.ofNat 42)

def finalOracle : FfiOracle Unit := fun _ _ _ _ => .final .diverged

def echoFfi : FfiState Unit := { oracle := echoOracle, state := (), ioEvents := [] }

def finalFfi : FfiState Unit := { oracle := finalOracle, state := (), ioEvents := [] }

def sourceLocals (name : Nat) : Option (PanWordLab (BitVec 64)) :=
  if name == 0 then some (.word 1) else
  if name == 1 then some (.word 0) else
  if name == 2 then some (.word 1) else
  if name == 3 then some (.word 8) else none

def sourceState (ffi : FfiState Unit) : CrepHolState (BitVec 64) Unit :=
  { locals := sourceLocals
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => true
    shMemaddrs := fun _ => false
    clock := 5
    bigEndian := false
    ffi := ffi
    baseAddress := 0
    topAddress := 100 }

def extCallReturnedMatches : Bool :=
  match evalCrepClockProg (.extCall "echo" 1 0 3 2) (sourceState echoFfi) with
  | (none, post) =>
      post.memory 8 == .word 42 && post.ffi.state == () &&
        post.ffi.ioEvents ==
          [{ name := .extCall "echo", configuration := [UInt8.ofNat 0],
             bytes := [(UInt8.ofNat 0, UInt8.ofNat 42)] }]
  | _ => false

def extCallFinalMatches : Bool :=
  match evalCrepClockProg (.extCall "live" 1 0 3 2) (sourceState finalFfi) with
  | (some (.finalFfi event), post) =>
      event.name == .extCall "live" &&
        event.configuration == [UInt8.ofNat 0] &&
        event.bytes == [UInt8.ofNat 0] && event.outcome == .diverged &&
        post.memory 8 == .word 0 && post.ffi.ioEvents.isEmpty
  | _ => false

def extCallMissingLocalMatches : Bool :=
  let state := { sourceState echoFfi with
    locals := fun name => if name == 0 then none else sourceLocals name }
  match evalCrepClockProg (.extCall "echo" 1 0 3 2) state with
  | (some .error, post) =>
      post.locals 0 == none && post.memory 8 == .word 0 &&
        post.ffi.ioEvents.isEmpty
  | _ => false

def extCallReadErrorMatches : Bool :=
  let state := { sourceState echoFfi with memaddrs := fun _ => false }
  match evalCrepClockProg (.extCall "echo" 1 0 3 2) state with
  | (some .error, post) =>
      post.locals 0 == some (.word 1) && post.memory 8 == .word 0 &&
        post.ffi.ioEvents.isEmpty
  | _ => false

#guard extCallReturnedMatches
#guard extCallFinalMatches
#guard extCallMissingLocalMatches
#guard extCallReadErrorMatches

def runChecks : IO Bool := do
  let ok := extCallReturnedMatches && extCallFinalMatches &&
    extCallMissingLocalMatches && extCallReadErrorMatches
  if extCallReturnedMatches then
    IO.println "PASS total Crep HOL ExtCall returned bytes and memory update match direct oracle"
  else
    IO.println "FAIL total Crep HOL ExtCall returned bytes and memory update match direct oracle"
  if extCallFinalMatches then
    IO.println "PASS total Crep HOL ExtCall final event preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall final event preserves state"
  if extCallMissingLocalMatches then
    IO.println "PASS total Crep HOL ExtCall missing-local Error preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall missing-local Error preserves state"
  if extCallReadErrorMatches then
    IO.println "PASS total Crep HOL ExtCall failed-read Error preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall failed-read Error preserves state"
  pure ok

end Flapjack.Test.CrepSemTotalExtCallParity
