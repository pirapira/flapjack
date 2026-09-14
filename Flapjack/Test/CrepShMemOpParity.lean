import Flapjack.CrepShMemOp
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$sh_mem_op_def`

The direct HOL fixture in `scripts/hol-probes/crep_sh_mem_op_probe.out`
checks representative load/store domain errors.  The executable checks pin
the source byte-count dispatch for all eight constructors through the FFI
configuration emitted by the exact raw-width transitions.
-/

namespace Flapjack.Test.CrepShMemOpParity

open Flapjack

def returningFfiState : FfiState Unit :=
  { natCrepRuntimeFfiState with
    oracle := fun _ state _ bytes => .returned state bytes }

def config (operator : CrepMemOp) : Option (List UInt8) :=
  match crepShMemOp { crepeRuntimeState with ffi := returningFfiState }
      operator 5 10 with
  | (.normal, state) => state.ffi.ioEvents.head?.map (·.configuration)
  | _ => none

#guard config .load == some [UInt8.ofNat 0]
#guard config .store == some [UInt8.ofNat 0]
#guard config .load8 == some [UInt8.ofNat 1]
#guard config .store8 == some [UInt8.ofNat 1]
#guard config .load16 == some [UInt8.ofNat 2]
#guard config .store16 == some [UInt8.ofNat 2]
#guard config .load32 == some [UInt8.ofNat 4]
#guard config .store32 == some [UInt8.ofNat 4]

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("crep sh_mem_op dispatches Load", config .load == some [UInt8.ofNat 0]),
    ("crep sh_mem_op dispatches Store", config .store == some [UInt8.ofNat 0]),
    ("crep sh_mem_op dispatches Load8", config .load8 == some [UInt8.ofNat 1]),
    ("crep sh_mem_op dispatches Store8", config .store8 == some [UInt8.ofNat 1]),
    ("crep sh_mem_op dispatches Load16", config .load16 == some [UInt8.ofNat 2]),
    ("crep sh_mem_op dispatches Store16", config .store16 == some [UInt8.ofNat 2]),
    ("crep sh_mem_op dispatches Load32", config .load32 == some [UInt8.ofNat 4]),
    ("crep sh_mem_op dispatches Store32", config .store32 == some [UInt8.ofNat 4])]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS {name}"
    else IO.println s!"FAIL {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.CrepShMemOpParity
