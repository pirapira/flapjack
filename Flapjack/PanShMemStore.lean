import Flapjack.PanShMemLoad

/-!
# Pancake `panSem.sh_mem_store`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:528-547`.

The source checks the unaligned address only for word widths, but always sends
the original address bytes to the mapped-write FFI.  Word bytes are truncated
only for nonzero widths; successful returns update only the FFI state.
-/

namespace Flapjack

inductive PanShMemStoreResult (α : Type u) (σ : Type v) where
  | error (state : PanShMemLoadState α σ)
  | normal (state : PanShMemLoadState α σ)
  | final (state : PanShMemLoadState α σ) (event : FfiFinalEvent)

def panShMemStore (context : PanValueFfiContext α)
    (state : PanShMemLoadState α σ) (value address : α)
    (size : OpSize) : PanShMemStoreResult α σ :=
  let width := panValueFfiWidth size
  let domainAddress := if width = 0 then address else context.byteAlign address
  if !context.sharedDomain domainAddress then
    .error state
  else
    let valueBytes := context.wordToBytes value false
    let addressBytes := context.wordToBytes address false
    let payload :=
      if width = 0 then valueBytes ++ addressBytes
      else valueBytes.take width ++ addressBytes
    match callFfi state.ffi (.sharedMem .mappedWrite) [UInt8.ofNat width] payload with
    | .returned nextFfi _ => .normal { state with ffi := nextFfi }
    | .final event => .final state event

end Flapjack
