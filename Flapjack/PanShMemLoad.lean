import Flapjack.PanValueFfiSemantics

/-!
# Pancake `panSem.sh_mem_load`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:510-524`.

The source checks the unaligned address only for word widths, but always sends
the original address bytes to the mapped-read FFI.  A successful return writes
the decoded word into the selected local/global map; a final FFI clears locals.
-/

namespace Flapjack

structure PanShMemLoadState (α : Type u) (σ : Type v) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)
  ffi : FfiState σ
  clock : Nat

inductive PanShMemLoadResult (α : Type u) (σ : Type v) where
  | error (state : PanShMemLoadState α σ)
  | normal (state : PanShMemLoadState α σ)
  | final (state : PanShMemLoadState α σ) (event : FfiFinalEvent)

def panShMemLoad (context : PanValueFfiContext α)
    (state : PanShMemLoadState α σ) (kind : VarKind) (name : VarName)
    (size : OpSize) (address : α) : PanShMemLoadResult α σ :=
  let width := panValueFfiWidth size
  let domainAddress := if width = 0 then address else context.byteAlign address
  if !context.sharedDomain domainAddress then
    .error state
  else
    match callFfi state.ffi (.sharedMem .mappedRead) [UInt8.ofNat width]
        (context.wordToBytes address false) with
    | .returned nextFfi bytes =>
        let value := PanValue.word (context.wordOfBytes false bytes)
        let state := { state with ffi := nextFfi }
        match kind with
        | .local => .normal { state with locals := updatePanValueMap state.locals name value }
        | .global => .normal { state with globals := updatePanValueMap state.globals name value }
    | .final event =>
        .final { state with locals := fun _ => none } event

end Flapjack
