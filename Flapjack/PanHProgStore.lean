import Flapjack.PanValueFfiSemantics
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_sh_mem_store`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:513-558`.
This boundary is parameterised by the two already-evaluated word operands,
which isolates the definition's own shared-memory/FFI behavior from the
separate `eval_def` port. It preserves the source rules: invalid operands or
an unmapped aligned address return `Error`; zero width uses the original
address and `valueBytes ++ addressBytes`; nonzero widths use the aligned
address only for the domain check and retain the original address bytes in
the payload; and the continuation maps a successful equal-length return to
normal, while mismatch/final oracle results become `FinalFFI` failures/events.
-/

namespace Flapjack

inductive PanHProgStoreResult (σ : Type u) where
  | normal
  | error
  | finalFfi (event : FfiFinalEvent)
  deriving DecidableEq, Repr

def panHProgStoreFinalEvent (configuration payload : List UInt8)
    (outcome : FfiOutcome) : FfiFinalEvent :=
  { name := .sharedMem .mappedWrite
    configuration := configuration
    bytes := payload
    outcome := outcome }

def panHProgShMemStore [BEq α]
    (context : PanValueFfiContext α) (size : OpSize)
    (address value : Option (PanValue α)) :
    PanFfiTree (PanHProgStoreResult σ) :=
  match address, value with
  | some (.word address), some (.word value) =>
      let width := panValueFfiWidth size
      let alignedAddress := if width = 0 then address else context.byteAlign address
      if !context.sharedDomain alignedAddress then
        .ret .error
      else
        let payload :=
          if width = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take width ++
              context.wordToBytes address false
        .vis (.sharedMem .mappedWrite) [UInt8.ofNat width] payload
          (fun response =>
            match response with
            | .returned bytes =>
                if bytes.length = payload.length then
                  .ret .normal
                else
                  .ret (.finalFfi (panHProgStoreFinalEvent [UInt8.ofNat width]
                    payload .failed))
            | .failed =>
                .ret (.finalFfi (panHProgStoreFinalEvent [UInt8.ofNat width]
                  payload .failed))
            | .final outcome =>
                .ret (.finalFfi (panHProgStoreFinalEvent [UInt8.ofNat width]
                  payload outcome)))
  | _, _ => .ret .error

@[simp] theorem panHProgShMemStore_invalid [BEq α]
    {σ : Type v}
    (context : PanValueFfiContext α)
    (size : OpSize) (address : Option (PanValue α)) :
    panHProgShMemStore (α := α) (σ := σ) context size address none =
      PanFfiTree.ret (α := PanHProgStoreResult σ)
        PanHProgStoreResult.error := by
  cases address <;> simp [panHProgShMemStore]

end Flapjack
