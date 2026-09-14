import Flapjack.CrepShMemStore
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$sh_mem_store_def`

The direct HOL fixture in `scripts/hol-probes/crep_sh_mem_store_probe.out`
checks missing-local and mapped-domain errors.  The executable cases cover
zero-width payload construction, aligned nonzero-width checking, unmapped
addresses, and final FFI state preservation.
-/

namespace Flapjack.Test.CrepShMemStoreParity

open Flapjack

def returningFfiState : FfiState Unit :=
  { natCrepRuntimeFfiState with
    oracle := fun _ state _ bytes => .returned state bytes }

def returnedStore : Bool :=
  match crepShMemStore { crepeRuntimeState with ffi := returningFfiState }
      5 10 0 with
  | (.normal, state) =>
      state.locals 5 == some 0 && state.ffi.ioEvents.length == 1 &&
        state.ffi.ioEvents.head?.map (·.configuration) == some [UInt8.ofNat 0]
  | _ => false

def alignedStore : Bool :=
  let state := { crepeRuntimeState with
    memoryModel := { natCrepRuntimeMemoryModel with
      byteAlign := fun _ _ => 0 },
    shMemaddrs := fun address => address == 0,
    ffi := returningFfiState }
  match crepShMemStore state 5 3 1 with
  | (.normal, state) =>
      state.ffi.ioEvents.head?.map (·.configuration) == some [UInt8.ofNat 1]
  | _ => false

def domainError : Bool :=
  match crepShMemStore
      { crepeRuntimeState with
        locals := fun name => if name == 5 then some 7 else none,
        shMemaddrs := fun _ => false }
      5 10 0 with
  | (.error, _) => true
  | _ => false

def missingLocal : Bool :=
  match crepShMemStore
      { crepeRuntimeState with locals := fun _ => none }
      5 10 0 with
  | (.error, _) => true
  | _ => false

def finalStore : Bool :=
  let finalFfi : FfiState Unit :=
    { natCrepRuntimeFfiState with
      oracle := fun _ _ _ _ => .final .failed }
  let state := { crepeRuntimeState with
    locals := fun name => if name == 5 then some 9 else none,
    ffi := finalFfi }
  match crepShMemStore state 5 10 0 with
  | (.finalFfi event, state) =>
      event.outcome == .failed && state.locals 5 == some 9
  | _ => false

#guard returnedStore
#guard alignedStore
#guard domainError
#guard missingLocal
#guard finalStore

def runChecks : IO Bool := do
  if returnedStore then IO.println "PASS crep sh_mem_store returns normally"
  else IO.println "FAIL crep sh_mem_store returns normally"
  if alignedStore then IO.println "PASS crep sh_mem_store checks aligned domain"
  else IO.println "FAIL crep sh_mem_store checks aligned domain"
  if domainError then IO.println "PASS crep sh_mem_store rejects unmapped address"
  else IO.println "FAIL crep sh_mem_store rejects unmapped address"
  if missingLocal then IO.println "PASS crep sh_mem_store rejects missing local"
  else IO.println "FAIL crep sh_mem_store rejects missing local"
  if finalStore then IO.println "PASS crep sh_mem_store preserves locals on final FFI"
  else IO.println "FAIL crep sh_mem_store preserves locals on final FFI"
  pure (returnedStore && alignedStore && domainError && missingLocal && finalStore)

end Flapjack.Test.CrepShMemStoreParity
