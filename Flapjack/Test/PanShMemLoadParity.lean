import Flapjack.PanShMemLoad

/-!
# Parity checks for `panSem$sh_mem_load_def`

The direct HOL fixture records both source domain-error branches.  Executable
checks cover the original-address payload after alignment, destination-map
updates, domain failure, length failure, and final-FFI local clearing.
-/

namespace Flapjack.Test.PanShMemLoadParity

open Flapjack

def byteContext (domain : Nat → Bool) (align : Nat → Nat) : PanValueFfiContext Nat :=
  { sharedDomain := domain
    byteAlign := align
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def returningFfi : FfiState Nat :=
  { oracle := fun _ state _ _ => .returned (state + 1) [9]
    state := 0
    ioEvents := [] }

def shortFfi : FfiState Nat :=
  { oracle := fun _ state _ _ => .returned state []
    state := 0
    ioEvents := [] }

def finalFfi : FfiState Nat :=
  { oracle := fun _ _ _ _ => .final .failed
    state := 0
    ioEvents := [] }

def initial : PanShMemLoadState Nat Nat :=
  { locals := fun name => if name == "old" then some (.word 4) else none
    globals := fun _ => none
    memory := fun _ => none
    ffi := returningFfi
    clock := 7 }

def returned : PanShMemLoadResult Nat Nat :=
  panShMemLoad (byteContext (fun address => address == 0) (fun _ => 0))
    initial .local "x" .op8 3

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def isNone : Option (PanValue Nat) → Bool
  | none => true
  | some _ => false

def alignedPayloadOriginal : Bool :=
  match returned with
  | .normal state =>
      isWord 9 (state.locals "x") &&
        isWord 4 (state.locals "old") &&
        state.ffi.state == 1 &&
        state.ffi.ioEvents == [{
          name := .sharedMem .mappedRead
          configuration := [1]
          bytes := [(3, 9)] }]
  | _ => false

def domainError : Bool :=
  match panShMemLoad (byteContext (fun _ => false) id)
      initial .local "x" .opW 3 with
  | .error state =>
      isWord 4 (state.locals "old") && state.clock == 7 &&
        state.ffi.state == 0 && state.ffi.ioEvents == []
  | _ => false

def lengthFailure : Bool :=
  match panShMemLoad (byteContext (fun _ => true) id)
      { initial with ffi := shortFfi } .local "x" .opW 3 with
  | .final state event => state.ffi.state == 0 && event.outcome == .failed
  | _ => false

def finalClearsLocals : Bool :=
  match panShMemLoad (byteContext (fun _ => true) id)
      { initial with ffi := finalFfi } .local "x" .opW 3 with
  | .final state _ => isNone (state.locals "old") && state.clock == 7
  | _ => false

#guard alignedPayloadOriginal
#guard domainError
#guard lengthFailure
#guard finalClearsLocals

def runChecks : IO Bool := do
  if alignedPayloadOriginal then IO.println "PASS Pan sh_mem_load original payload after alignment"
  else IO.println "FAIL Pan sh_mem_load original payload after alignment"
  if domainError then IO.println "PASS Pan sh_mem_load domain error"
  else IO.println "FAIL Pan sh_mem_load domain error"
  if lengthFailure then IO.println "PASS Pan sh_mem_load length failure"
  else IO.println "FAIL Pan sh_mem_load length failure"
  if finalClearsLocals then IO.println "PASS Pan sh_mem_load final clears locals"
  else IO.println "FAIL Pan sh_mem_load final clears locals"
  pure (alignedPayloadOriginal && domainError && lengthFailure && finalClearsLocals)

end Flapjack.Test.PanShMemLoadParity
