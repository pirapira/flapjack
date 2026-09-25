import Flapjack.Ffi
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef

/-!
# Exact HOL `ffi_state` carrier

Lean counterpart of `cakeml/semantics/ffi/ffiScript.sml:15-61`.  That script
defines the observable FFI boundary used by the CakeML semantics:

```
Datatype ffi_outcome = FFI_failed | FFI_diverged
Datatype oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
Datatype shmem_op = MappedRead | MappedWrite
Datatype ffiname = ExtCall mlstring | SharedMem shmem_op
Type oracle_function = :'ffi -> word8 list -> word8 list -> 'ffi oracle_result
Type oracle = :ffiname -> 'ffi oracle_function
Datatype io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
Datatype final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
Datatype ffi_state = <| oracle; ffi_state; io_events |>
Definition initial_ffi_state oc ffi = <| oracle := oc; ffi_state := ffi; io_events := [] |>
Datatype ffi_result = FFI_return ('ffi ffi_state) (word8 list) | FFI_final final_event
```

The carriers below fix the differences from the executable
`Flapjack.Ffi` module: `word8` is the canonical 256-element `BitVec 8` (not
`UInt8`), the external-call name is the exact `mlstring` carrier (not Lean
`String`), and the `ffi_state` field is named `ffiState` mirroring HOL
`ffi_state` (the executable record calls it `state`).  The declarations are
shape-exact ports, tagged against the HOL script.

The executable `FfiState`/`callFfi` boundary and a checked relation to these
carriers (byte codecs for `UInt8`/`BitVec 8` and `String`/`MlString`, plus the
name/event correspondence) are tracked by the same bead
(`flapjack-pxn.18.5.17.1.2`); this module provides the exact source carrier and
a direct HOL oracle for it.
-/

namespace Flapjack

/-- Exact port of HOL `Datatype: ffi_outcome = FFI_failed | FFI_diverged`
    (`cakeml/semantics/ffi/ffiScript.sml:15-17`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_outcome"]
inductive HolFfiOutcome where
  | failed
  | diverged
  deriving DecidableEq, Repr

/-- Exact port of HOL `Datatype: oracle_result = Oracle_return 'ffi (word8 list)
    | Oracle_final ffi_outcome` (`cakeml/semantics/ffi/ffiScript.sml:19-21`).
    Constructor arity and field order match: the returned constructor carries
    the new `'ffi` state first and the byte list second. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle_result"]
inductive HolOracleResult (σ : Type u) where
  | ret (value : σ) (bytes : List (BitVec 8))
  | final (outcome : HolFfiOutcome)
  deriving Repr

/-- Exact port of HOL `Datatype: shmem_op = MappedRead | MappedWrite`
    (`cakeml/semantics/ffi/ffiScript.sml:23-25`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "shmem_op"]
inductive HolShmemOp where
  | mappedRead
  | mappedWrite
  deriving DecidableEq, Repr

/-- Exact port of HOL `Datatype: ffiname = ExtCall mlstring | SharedMem shmem_op`
    (`cakeml/semantics/ffi/ffiScript.sml:27-29`).  The external-call name is the
    faithful `MlString` carrier. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffiname"]
inductive HolFfiName where
  | extCall (name : Flapjack.Basis.Pure.MlString.MlString)
  | sharedMem (operator : HolShmemOp)
  deriving DecidableEq, Repr

/-- Exact port of HOL
    `Type oracle_function = :'ffi -> word8 list -> word8 list -> 'ffi oracle_result`
    (`cakeml/semantics/ffi/ffiScript.sml:31`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle_function"]
abbrev HolOracleFunction (σ : Type u) :=
  σ → List (BitVec 8) → List (BitVec 8) → HolOracleResult σ

/-- Exact port of HOL `Type oracle = :ffiname -> 'ffi oracle_function`
    (`cakeml/semantics/ffi/ffiScript.sml:32`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle"]
abbrev HolOracle (σ : Type u) := HolFfiName → HolOracleFunction σ

/-- Exact port of HOL
    `Datatype io_event = IO_event ffiname (word8 list) ((word8 # word8) list)`
    (`cakeml/semantics/ffi/ffiScript.sml:41-42`).  The final field is the
    mutable-array map `(input, output)` as in HOL `ZIP (bytes, bytes')`. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "io_event"]
structure HolIoEvent where
  name : HolFfiName
  configuration : List (BitVec 8)
  bytes : List (BitVec 8 × BitVec 8)
  deriving DecidableEq, Repr

/-- Exact port of HOL
    `Datatype final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome`
    (`cakeml/semantics/ffi/ffiScript.sml:44-46`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "final_event"]
structure HolFinalEvent where
  name : HolFfiName
  configuration : List (BitVec 8)
  bytes : List (BitVec 8)
  outcome : HolFfiOutcome
  deriving Repr

/-- Exact port of HOL
    `Datatype ffi_state = <| oracle; ffi_state; io_events |>`
    (`cakeml/semantics/ffi/ffiScript.sml:48-52`).  Field order matches HOL:
    oracle, host state, event list. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_state"]
structure HolFfiState (σ : Type u) where
  oracle : HolOracle σ
  ffiState : σ
  ioEvents : List HolIoEvent

/-- Exact port of HOL
    `Definition initial_ffi_state oc ffi = <| oracle := oc; ffi_state := ffi; io_events := [] |>`
    (`cakeml/semantics/ffi/ffiScript.sml:55-57`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "initial_ffi_state_def"]
def initialHolFfiState (oracle : HolOracle σ) (state : σ) : HolFfiState σ :=
  { oracle := oracle, ffiState := state, ioEvents := [] }

/-- Exact port of HOL
    `Datatype ffi_result = FFI_return ('ffi ffi_state) (word8 list) | FFI_final final_event`
    (`cakeml/semantics/ffi/ffiScript.sml:59-61`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_result"]
inductive HolFfiResult (σ : Type u) where
  | ret (state : HolFfiState σ) (bytes : List (BitVec 8))
  | final (event : HolFinalEvent)

/-- Exact port of HOL
    `Definition call_FFI st s conf bytes = if s <> ExtCall «» then ... else FFI_return st bytes`
    (`cakeml/semantics/ffi/ffiScript.sml:65-73`).  The empty external-call name is
    the special identity call; a successful oracle return appends an `io_event`
    with `ZIP (bytes, bytes')`, and a length mismatch or terminal oracle result
    becomes `FFI_final`. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "call_FFI_def"]
def callFFIHOL (state : HolFfiState σ) (name : HolFfiName)
    (configuration bytes : List (BitVec 8)) : HolFfiResult σ :=
  if name = .extCall (Flapjack.Basis.Pure.MlString.MlString.implode []) then
    .ret state bytes
  else
    match state.oracle name state.ffiState configuration bytes with
    | .ret nextState nextBytes =>
        if nextBytes.length = bytes.length then
          .ret
            { state with
              ffiState := nextState
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

end Flapjack