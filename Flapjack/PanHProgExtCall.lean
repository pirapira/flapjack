import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_ext_call`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:415-443`.
The expression evaluation, byte-array reads, and memory write are represented
by their already-computed inputs and an explicit `writeArray` projection.
This keeps the source FFI boundary exact: empty names are local identity
writes, nonempty names emit `ExtCall`, equal-length returns write returned
bytes, and mismatch/final outcomes clear through `emptyState`.
-/

namespace Flapjack

inductive PanHProgExtCallResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  | finalFfi (sourceState : σ) (event : FfiFinalEvent)
  deriving Repr

def panHProgExtCallFinalEvent (function : FunName)
    (configuration payload : List UInt8) (outcome : FfiOutcome) : FfiFinalEvent :=
  { name := .extCall function
    configuration := configuration
    bytes := payload
    outcome := outcome }

def panHProgExtCall [BEq String]
    (sourceState emptyState : σ) (writeArray : σ → List UInt8 → σ)
    (function : FunName) (configuration payload : Option (List UInt8)) :
    PanFfiTree (PanHProgExtCallResult σ) :=
  match configuration, payload with
  | some configuration, some payload =>
      if function == "" then
        .ret (.normal (writeArray sourceState payload))
      else
        .vis (.extCall function) configuration payload
          (fun response =>
            match response with
            | .returned bytes =>
                if bytes.length = payload.length then
                  .ret (.normal (writeArray sourceState bytes))
                else
                  .ret (.finalFfi emptyState (panHProgExtCallFinalEvent
                    function configuration payload .failed))
            | .failed =>
                .ret (.finalFfi emptyState (panHProgExtCallFinalEvent
                  function configuration payload .failed))
            | .final outcome =>
                .ret (.finalFfi emptyState (panHProgExtCallFinalEvent
                  function configuration payload outcome)))
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgExtCall_invalid [BEq String]
    (sourceState emptyState : σ) (writeArray : σ → List UInt8 → σ)
    (function : FunName) (configuration : Option (List UInt8)) :
    panHProgExtCall sourceState emptyState writeArray function configuration none =
      PanFfiTree.ret (α := PanHProgExtCallResult σ)
        (PanHProgExtCallResult.error sourceState) := by
  cases configuration <;> simp [panHProgExtCall]

end Flapjack
