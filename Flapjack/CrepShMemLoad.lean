import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.sh_mem_load`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:168-184`.

The direct transition below takes the source byte count: width zero checks the
original address, nonzero widths check the byte-aligned address, while the FFI
receives the original address bytes.  A returned call inserts the decoded word
into the destination local and updates FFI state; a final call returns
`FinalFFI` and clears locals, exactly as the source does.  The existing
`crepRuntimeSharedMem` is the operator-indexed evaluator adapter for the same
four widths used by `sh_mem_op`.
-/

namespace Flapjack

def crepRuntimeShMemLoad (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    CrepRuntimeStep α σ FfiFinalEvent :=
  let alignedAddress :=
    if width = 0 then address
    else state.memoryModel.byteAlign state.bytesInWord address
  if !state.shMemaddrs alignedAddress then
    (.error, state)
  else
    match callFfi state.ffi (.sharedMem .mappedRead)
        [UInt8.ofNat width]
        (state.ffiContext.wordToBytes
          (if width = 0 then alignedAddress else address) false) with
    | .final event =>
        (.finalFfi event, clearCrepRuntimeLocals state)
    | .returned ffi bytes =>
        let value := state.ffiContext.wordOfBytes false bytes
        let state := { state with ffi := ffi }
        (.normal, { state with locals := updateCrepLocal state.locals name value })

def crepShMemLoad (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    CrepRuntimeStep α σ FfiFinalEvent :=
  crepRuntimeShMemLoad state name address width

@[simp] theorem crepShMemLoad_eq_runtime (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    crepShMemLoad state name address width =
      crepRuntimeShMemLoad state name address width := by
  rfl

end Flapjack
