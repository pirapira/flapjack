import Flapjack.Language

/-!
# CakeML's observable FFI boundary

This is the Lean counterpart of `cakeml/semantics/ffi/ffiScript.sml`.
The oracle is parameterised by the host state, while the compiler-visible
payload is a byte list.  Successful calls append an observable event and
return the oracle's new host state and bytes.  A length mismatch or an oracle
terminal result becomes a terminal event; the empty external-call name is the
special identity call used by CakeML.
-/

namespace Flapjack

inductive FfiOutcome where
  | failed
  | diverged
  deriving DecidableEq, Repr

inductive FfiOracleResult (σ : Type u) where
  | returned (state : σ) (bytes : List UInt8)
  | final (outcome : FfiOutcome)
  deriving Repr

inductive FfiShmemOp where
  | mappedRead
  | mappedWrite
  deriving DecidableEq, Repr

inductive FfiName where
  | extCall (name : FunName)
  | sharedMem (operator : FfiShmemOp)
  deriving DecidableEq, Repr

abbrev FfiOracle (σ : Type u) :=
  FfiName → σ → List UInt8 → List UInt8 → FfiOracleResult σ

structure FfiEvent where
  name : FfiName
  configuration : List UInt8
  bytes : List (UInt8 × UInt8)
  deriving DecidableEq, Repr

structure FfiFinalEvent where
  name : FfiName
  configuration : List UInt8
  bytes : List UInt8
  outcome : FfiOutcome
  deriving DecidableEq, Repr

structure FfiState (σ : Type u) where
  oracle : FfiOracle σ
  state : σ
  ioEvents : List FfiEvent

inductive FfiResult (σ : Type u) where
  | returned (state : FfiState σ) (bytes : List UInt8)
  | final (event : FfiFinalEvent)

def callFfi (state : FfiState σ) (name : FfiName)
    (configuration bytes : List UInt8) : FfiResult σ :=
  if name = .extCall "" then
    .returned state bytes
  else
    match state.oracle name state.state configuration bytes with
    | .returned nextState nextBytes =>
        if nextBytes.length = bytes.length then
          .returned
            { state with
              state := nextState
              ioEvents := state.ioEvents ++
                [{ name := name, configuration := configuration,
                   bytes := bytes.zip nextBytes }] }
            nextBytes
        else
          .final
            { name := name, configuration := configuration, bytes := bytes,
              outcome := .failed }
    | .final outcome =>
        .final
          { name := name, configuration := configuration, bytes := bytes,
            outcome := outcome }

theorem callFfi_empty_extCall (state : FfiState σ)
    (configuration bytes : List UInt8) :
    callFfi state (.extCall "") configuration bytes =
      .returned state bytes := by
  simp [callFfi]

theorem callFfi_oracle_return (state : FfiState σ)
    (name : FfiName) (configuration bytes nextBytes : List UInt8)
    (nextState : σ) (hname : name ≠ .extCall "")
    (hlength : nextBytes.length = bytes.length)
    (horacle : state.oracle name state.state configuration bytes =
      .returned nextState nextBytes) :
    callFfi state name configuration bytes =
      .returned
        { state with
          state := nextState
          ioEvents := state.ioEvents ++
            [{ name := name, configuration := configuration,
               bytes := bytes.zip nextBytes }] }
        nextBytes := by
  simp [callFfi, hname, horacle, hlength]

theorem callFfi_oracle_length_failure (state : FfiState σ)
    (name : FfiName) (configuration bytes nextBytes : List UInt8)
    (nextState : σ) (hname : name ≠ .extCall "")
    (hlength : nextBytes.length ≠ bytes.length)
    (horacle : state.oracle name state.state configuration bytes =
      .returned nextState nextBytes) :
    callFfi state name configuration bytes =
      .final
        { name := name, configuration := configuration, bytes := bytes,
          outcome := .failed } := by
  simp [callFfi, hname, horacle, hlength]

theorem callFfi_oracle_final (state : FfiState σ)
    (name : FfiName) (configuration bytes : List UInt8)
    (outcome : FfiOutcome) (hname : name ≠ .extCall "")
    (horacle : state.oracle name state.state configuration bytes =
      .final outcome) :
    callFfi state name configuration bytes =
      .final
        { name := name, configuration := configuration, bytes := bytes,
          outcome := outcome } := by
  simp [callFfi, hname, horacle]

end Flapjack
