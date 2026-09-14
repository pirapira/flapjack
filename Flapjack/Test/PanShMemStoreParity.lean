import Flapjack.PanShMemStore

/-!
# Parity checks for `panSem$sh_mem_store_def`

The direct HOL fixture records both source domain-error branches.  Executable
checks cover original-address payloads after alignment, width truncation,
domain failure, length failure, and final-FFI state preservation.
-/

namespace Flapjack.Test.PanShMemStoreParity

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
  { oracle := fun _ state _ _ => .returned (state + 1) [0, 0]
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

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def zeroWidth : PanShMemStoreResult Nat Nat :=
  panShMemStore (byteContext (fun _ => true) id) initial 7 3 .opW

def alignedWidth : PanShMemStoreResult Nat Nat :=
  panShMemStore (byteContext (fun address => address == 0) (fun _ => 0))
    initial 7 3 .op8

def payloadIs (state : PanShMemLoadState Nat Nat) (configuration : List UInt8)
    (payload : List (UInt8 × UInt8)) : Bool :=
  state.ffi.ioEvents == [{
    name := .sharedMem .mappedWrite
    configuration := configuration
    bytes := payload }]

def zeroWidthPayload : Bool :=
  match zeroWidth with
  | .normal state =>
      state.ffi.state == 1 && payloadIs state [0] [(7, 0), (3, 0)]
  | _ => false

def alignedOriginalPayload : Bool :=
  match alignedWidth with
  | .normal state =>
      state.ffi.state == 1 && payloadIs state [1] [(7, 0), (3, 0)]
  | _ => false

def domainError : Bool :=
  match panShMemStore (byteContext (fun _ => false) id)
      initial 7 3 .opW with
  | .error state =>
      isWord 4 (state.locals "old") && state.clock == 7 &&
        state.ffi.state == 0 && state.ffi.ioEvents == []
  | _ => false

def lengthFailure : Bool :=
  match panShMemStore (byteContext (fun _ => true) id)
      { initial with ffi := shortFfi } 7 3 .opW with
  | .final state event => state.ffi.state == 0 && event.outcome == .failed
  | _ => false

def finalPreservesState : Bool :=
  match panShMemStore (byteContext (fun _ => true) id)
      { initial with ffi := finalFfi } 7 3 .opW with
  | .final state _ => isWord 4 (state.locals "old") && state.clock == 7
  | _ => false

#guard zeroWidthPayload
#guard alignedOriginalPayload
#guard domainError
#guard lengthFailure
#guard finalPreservesState

def runChecks : IO Bool := do
  if zeroWidthPayload then IO.println "PASS Pan sh_mem_store zero-width payload"
  else IO.println "FAIL Pan sh_mem_store zero-width payload"
  if alignedOriginalPayload then IO.println "PASS Pan sh_mem_store original payload after alignment"
  else IO.println "FAIL Pan sh_mem_store original payload after alignment"
  if domainError then IO.println "PASS Pan sh_mem_store domain error"
  else IO.println "FAIL Pan sh_mem_store domain error"
  if lengthFailure then IO.println "PASS Pan sh_mem_store length failure"
  else IO.println "FAIL Pan sh_mem_store length failure"
  if finalPreservesState then IO.println "PASS Pan sh_mem_store final preserves state"
  else IO.println "FAIL Pan sh_mem_store final preserves state"
  pure (zeroWidthPayload && alignedOriginalPayload && domainError &&
    lengthFailure && finalPreservesState)

end Flapjack.Test.PanShMemStoreParity
