import Flapjack.CrepShMemOp
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$sh_mem_op_def`

The direct HOL fixture records that all eight source constructors dispatch to
the corresponding byte count.  The executable checks observe the FFI
configuration and verify that both load and store families preserve the
source operator while selecting widths 0, 1, 2, and 4.
-/

namespace Flapjack.Test.CrepShMemOpParity

open Flapjack

def echoHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request ffi =>
    match request with
    | .sharedMem operator _ _ bytes =>
        .returned
          { ffi with ioEvents := ffi.ioEvents ++ [{
              name := .sharedMem .mappedRead,
              configuration := [UInt8.ofNat (crepRuntimeMemWidth operator)],
              bytes := [] }] }
          (match operator with
          | .load | .load8 | .load16 | .load32 => [UInt8.ofNat 3]
          | .store | .store8 | .store16 | .store32 => bytes)
    | .extCall _ _ _ => .returned ffi []

def probeState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    locals := fun name => if name == 1 then some 7 else none
    shMemaddrs := fun _ => true }

def configuration (operator : CrepMemOp) : Option (List UInt8) :=
  match crepShMemOp echoHandler probeState operator 1 3 with
  | (.normal, state) => state.ffi.ioEvents.head?.map (·.configuration)
  | _ => none

def loadValue : Bool :=
  match crepShMemOp echoHandler probeState .load 1 3 with
  | (.normal, state) => state.locals 1 == some 3
  | _ => false

def storeResult : Bool :=
  match crepShMemOp echoHandler probeState .store 1 3 with
  | (.normal, state) => state.locals 1 == some 7
  | _ => false

#guard configuration .load == some [UInt8.ofNat 0]
#guard configuration .store == some [UInt8.ofNat 0]
#guard configuration .load8 == some [UInt8.ofNat 1]
#guard configuration .store8 == some [UInt8.ofNat 1]
#guard configuration .load16 == some [UInt8.ofNat 2]
#guard configuration .store16 == some [UInt8.ofNat 2]
#guard configuration .load32 == some [UInt8.ofNat 4]
#guard configuration .store32 == some [UInt8.ofNat 4]
#guard loadValue
#guard storeResult

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("sh_mem_op dispatches Load with width zero",
      configuration .load == some [UInt8.ofNat 0]),
    ("sh_mem_op dispatches Store with width zero",
      configuration .store == some [UInt8.ofNat 0]),
    ("sh_mem_op dispatches Load8",
      configuration .load8 == some [UInt8.ofNat 1]),
    ("sh_mem_op dispatches Store8",
      configuration .store8 == some [UInt8.ofNat 1]),
    ("sh_mem_op dispatches Load16",
      configuration .load16 == some [UInt8.ofNat 2]),
    ("sh_mem_op dispatches Store16",
      configuration .store16 == some [UInt8.ofNat 2]),
    ("sh_mem_op dispatches Load32",
      configuration .load32 == some [UInt8.ofNat 4]),
    ("sh_mem_op dispatches Store32",
      configuration .store32 == some [UInt8.ofNat 4]),
    ("sh_mem_op load preserves the returned value",
      loadValue),
    ("sh_mem_op store preserves the state",
      storeResult)]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS crep {name}"
    else IO.println s!"FAIL crep {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.CrepShMemOpParity
