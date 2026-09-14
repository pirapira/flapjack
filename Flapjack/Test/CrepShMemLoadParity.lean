import Flapjack.CrepShMemLoad
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$sh_mem_load_def`

The direct HOL fixture in `scripts/hol-probes/crep_sh_mem_load_probe.out`
checks the source's zero/nonzero mapped-domain errors.  The executable cases
cover a returned word, an aligned nonzero-width access, an unmapped address,
and a final FFI response that clears locals.
-/

namespace Flapjack.Test.CrepShMemLoadParity

open Flapjack

def returnedFfiState : FfiState Unit :=
  { natCrepRuntimeFfiState with
    oracle := fun _ state _ _ => .returned state [7] }

def returnedLoad : Bool :=
  match crepShMemLoad { crepeRuntimeState with ffi := returnedFfiState }
      5 10 0 with
  | (.normal, state) =>
      state.locals 5 == some 7 && state.ffi.ioEvents.length == 1
  | _ => false

def alignedLoad : Bool :=
  let state := { crepeRuntimeState with
    memoryModel := { natCrepRuntimeMemoryModel with
      byteAlign := fun _ _ => 0 },
    shMemaddrs := fun address => address == 0 }
  match crepShMemLoad { state with ffi := returnedFfiState } 5 3 1 with
  | (.normal, state) =>
      state.locals 5 == some 7 && state.ffi.ioEvents.length == 1
  | _ => false

def domainError : Bool :=
  match crepShMemLoad
      { crepeRuntimeState with shMemaddrs := fun _ => false }
      5 10 0 with
  | (.error, _) => true
  | _ => false

def finalLoad : Bool :=
  let finalFfi : FfiState Unit :=
    { natCrepRuntimeFfiState with
      oracle := fun _ _ _ _ => .final .failed }
  let state := { crepeRuntimeState with
    locals := fun name => if name == 5 then some 9 else none,
    ffi := finalFfi }
  match crepShMemLoad state 5 10 0 with
  | (.finalFfi event, state) =>
      event.outcome == .failed && state.locals 5 == none
  | _ => false

#guard returnedLoad
#guard alignedLoad
#guard domainError
#guard finalLoad

def runChecks : IO Bool := do
  if returnedLoad then IO.println "PASS crep sh_mem_load returns a word"
  else IO.println "FAIL crep sh_mem_load returns a word"
  if alignedLoad then IO.println "PASS crep sh_mem_load checks aligned domain"
  else IO.println "FAIL crep sh_mem_load checks aligned domain"
  if domainError then IO.println "PASS crep sh_mem_load rejects unmapped address"
  else IO.println "FAIL crep sh_mem_load rejects unmapped address"
  if finalLoad then IO.println "PASS crep sh_mem_load clears locals on final FFI"
  else IO.println "FAIL crep sh_mem_load clears locals on final FFI"
  pure (returnedLoad && alignedLoad && domainError && finalLoad)

end Flapjack.Test.CrepShMemLoadParity
