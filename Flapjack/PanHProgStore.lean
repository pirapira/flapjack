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
The source bstate is unchanged by this definition, so every result carries an
opaque source-state token through the corresponding return branch.
-/

namespace Flapjack

inductive PanHProgStoreResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  | finalFfi (sourceState : σ) (event : FfiFinalEvent)
  deriving Repr

def panHProgStoreState : PanHProgStoreResult σ → σ
  | .normal sourceState => sourceState
  | .error sourceState => sourceState
  | .finalFfi sourceState _ => sourceState

def panHProgStoreFinalEvent (configuration payload : List UInt8)
    (outcome : FfiOutcome) : FfiFinalEvent :=
  { name := .sharedMem .mappedWrite
    configuration := configuration
    bytes := payload
    outcome := outcome }

def panHProgStoreResponse (sourceState : σ) (configuration payload : List UInt8)
    (response : PanFfiResponse) : PanHProgStoreResult σ :=
  match response with
  | .returned bytes =>
      if bytes.length = payload.length then
        .normal sourceState
      else
        .finalFfi sourceState (panHProgStoreFinalEvent configuration payload .failed)
  | .failed =>
      .finalFfi sourceState (panHProgStoreFinalEvent configuration payload .failed)
  | .final outcome =>
      .finalFfi sourceState (panHProgStoreFinalEvent configuration payload outcome)

/-! Kernel-checked source-state projection for every `Vis` continuation
    installed by `panHProgShMemStore`. -/
@[simp] theorem panHProgStoreResponse_state (sourceState : σ)
    (configuration payload : List UInt8) (response : PanFfiResponse) :
    panHProgStoreState (panHProgStoreResponse sourceState configuration payload response) =
      sourceState := by
  cases response with
  | returned bytes =>
      by_cases h : bytes.length = payload.length
      · simp [panHProgStoreResponse, panHProgStoreState, h]
      · simp [panHProgStoreResponse, panHProgStoreState, h]
  | failed => simp [panHProgStoreResponse, panHProgStoreState]
  | final outcome => simp [panHProgStoreResponse, panHProgStoreState]

def panHProgShMemStore [BEq α]
    (context : PanValueFfiContext α) (sourceState : σ) (size : OpSize)
    (address value : Option (PanValue α)) :
    PanFfiTree (PanHProgStoreResult σ) :=
  match address, value with
  | some (.word address), some (.word value) =>
      let width := panValueFfiWidth size
      let alignedAddress := if width = 0 then address else context.byteAlign address
      if !context.sharedDomain alignedAddress then
        .ret (.error sourceState)
      else
        let payload :=
          if width = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take width ++
              context.wordToBytes address false
        .vis (.sharedMem .mappedWrite) [UInt8.ofNat width] payload
          (fun response =>
            .ret (panHProgStoreResponse sourceState [UInt8.ofNat width] payload response))
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgShMemStore_invalid [BEq α]
    {σ : Type v}
    (context : PanValueFfiContext α) (sourceState : σ)
    (size : OpSize) (address : Option (PanValue α)) :
    panHProgShMemStore (α := α) (σ := σ) context sourceState size address none =
      PanFfiTree.ret (α := PanHProgStoreResult σ)
        (PanHProgStoreResult.error sourceState) := by
  cases address <;> simp [panHProgShMemStore]

end Flapjack
