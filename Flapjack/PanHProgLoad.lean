import Flapjack.PanValueFfiSemantics
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_sh_mem_load`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:466-513`.
The definition is parameterised by the already-evaluated address and the
destination lookup result, isolating its shared-memory/FFI boundary from the
separate `eval` and `lookup_kvar` ports.  It preserves the source behavior:
the aligned address is used only for the nonzero-width domain check, the FFI
payload always contains the original address bytes, successful returns update
the destination, and final/mismatched returns clear locals through the
explicit `emptyState` projection.
-/

namespace Flapjack

inductive PanHProgLoadResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  | finalFfi (sourceState : σ) (event : FfiFinalEvent)
  deriving Repr

def panHProgLoadFinalEvent (configuration payload : List UInt8)
    (outcome : FfiOutcome) : FfiFinalEvent :=
  { name := .sharedMem .mappedRead
    configuration := configuration
    bytes := payload
    outcome := outcome }

def panHProgShMemLoad [BEq α]
    (context : PanValueFfiContext α)
    (sourceState emptyState : σ) (setDestination : σ → α → σ)
    (size : OpSize) (address : Option (PanValue α))
    (destination : Option (PanValue α)) :
    PanFfiTree (PanHProgLoadResult σ) :=
  match address, destination with
  | some (.word address), some _ =>
      let width := panValueFfiWidth size
      let alignedAddress := if width = 0 then address else context.byteAlign address
      let payload := context.wordToBytes address false
      if !context.sharedDomain alignedAddress then
        .ret (.error sourceState)
      else
        .vis (.sharedMem .mappedRead) [UInt8.ofNat width] payload
          (fun response =>
            match response with
            | .returned bytes =>
                if bytes.length = payload.length then
                  .ret (.normal (setDestination sourceState
                    (context.wordOfBytes false bytes)))
                else
                  .ret (.finalFfi emptyState (panHProgLoadFinalEvent
                    [UInt8.ofNat width] payload .failed))
            | .failed =>
                .ret (.finalFfi emptyState (panHProgLoadFinalEvent
                  [UInt8.ofNat width] payload .failed))
            | .final outcome =>
                .ret (.finalFfi emptyState (panHProgLoadFinalEvent
                  [UInt8.ofNat width] payload outcome)))
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgShMemLoad_invalid [BEq α]
    {σ : Type v}
    (context : PanValueFfiContext α)
    (sourceState emptyState : σ) (setDestination : σ → α → σ)
    (size : OpSize) (address : Option (PanValue α)) :
    panHProgShMemLoad (α := α) context sourceState emptyState setDestination
        size address none =
      PanFfiTree.ret (α := PanHProgLoadResult σ)
        (PanHProgLoadResult.error sourceState) := by
  cases address <;> simp [panHProgShMemLoad]

end Flapjack
