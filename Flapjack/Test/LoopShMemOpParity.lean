import Flapjack.LoopFfi

/-!
# Original-domain parity for `loopSem$sh_mem_op`

Reference: `cakeml/pancake/semantics/loopSemScript.sml:255-262`.
The source fixture `scripts/hol-probes/loop_sem_sh_mem_op_probe.out` records the
byte-count configuration selected by all eight load/store constructors.
-/

namespace Flapjack.Test.LoopShMemOpParity

open Flapjack

def probeState : LoopFfiState Nat Unit :=
  { locals := fun name => if name == 1 then some 7 else none
    globals := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    byteAlign := id
    clock := 10
    bigEndian := false
    baseAddress := 0
    topAddress := 0
    ffi :=
      { oracle := fun _ state _ bytes => .returned state bytes
        state := ()
        ioEvents := [] }
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    valueToNat := id }

def config (operator : CrepMemOp) : Option (List UInt8) :=
  match loopFfiShMemOp probeState operator 1 3 with
  | (.normal state, _) => state.ffi.ioEvents.head?.map (·.configuration)
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
    ("sh_mem_op dispatches Load with width zero",
      config .load == some [UInt8.ofNat 0]),
    ("sh_mem_op dispatches Store with width zero",
      config .store == some [UInt8.ofNat 0]),
    ("sh_mem_op dispatches Load8",
      config .load8 == some [UInt8.ofNat 1]),
    ("sh_mem_op dispatches Store8",
      config .store8 == some [UInt8.ofNat 1]),
    ("sh_mem_op dispatches Load16",
      config .load16 == some [UInt8.ofNat 2]),
    ("sh_mem_op dispatches Store16",
      config .store16 == some [UInt8.ofNat 2]),
    ("sh_mem_op dispatches Load32",
      config .load32 == some [UInt8.ofNat 4]),
    ("sh_mem_op dispatches Store32",
      config .store32 == some [UInt8.ofNat 4])]
  let results ← checks.mapM fun (name, passed) => do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.LoopShMemOpParity
