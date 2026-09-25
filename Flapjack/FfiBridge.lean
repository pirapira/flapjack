import Flapjack.Ffi
import Flapjack.FfiHOL
import Flapjack.HolRef

/-!
# Bridge between the executable FFI state and the exact HOL `ffi_state`

`Flapjack/Ffi.lean` is the executed CakeML FFI boundary: it uses `UInt8`
payload bytes, `String` external-call names (`FunName`) and the fields
`state`/`ioEvents`.  `Flapjack/FfiHOL.lean` ports the exact HOL carriers from
`cakeml/semantics/ffi/ffiScript.sml`: `word8 = BitVec 8` bytes, `mlstring`
names and the fields `ffiState`/`ioEvents`.

This module gives the checked relation between the two representations plus an
executable bridge for `callFfi`/`callFFI_FFI` on the identity external call.
The byte relation is expressed through `Nat` values so it is exact on the
range both representations cover; the name relation maps a `String` external
call name to the byte codec `MlString.ofString`.  The relation is
Flapjack-specific infrastructure (the HOL source has no separate compiled
carrier), so nothing here is tagged.
-/

namespace Flapjack

/-- Production byte to HOL `word8`. -/
def byteToBits (value : UInt8) : BitVec 8 := BitVec.ofNat 8 value.toNat

/-- HOL `word8` to production byte. -/
def bitsToByte (value : BitVec 8) : UInt8 := UInt8.ofNat value.toNat

theorem byteToBits_toNat (value : UInt8) : (byteToBits value).toNat = value.toNat := by
  rw [byteToBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt value)]

theorem bitsToByte_byteToBits (value : UInt8) : bitsToByte (byteToBits value) = value := by
  rw [bitsToByte, byteToBits_toNat, UInt8.ofNat_toNat]

/-- Byte-list relation: the HOL list has the same `Nat` values as the production list. -/
def BytesRel (prod : List UInt8) (hol : List (BitVec 8)) : Prop :=
  hol.map BitVec.toNat = prod.map UInt8.toNat

theorem bytesRel_map_byteToBits (bytes : List UInt8) : BytesRel bytes (bytes.map byteToBits) := by
  simp [BytesRel, List.map_map, byteToBits_toNat]

/-- The HOL `word8` pair list relation used by `io_event`. -/
def BytesPairRel (prod : List (UInt8 × UInt8)) (hol : List (BitVec 8 × BitVec 8)) : Prop :=
  hol.map (fun pair => (pair.1.toNat, pair.2.toNat)) =
    prod.map (fun pair => (pair.1.toNat, pair.2.toNat))

/-- FFI outcome relation. -/
def OutcomeRel (prod : FfiOutcome) (hol : HolFfiOutcome) : Prop :=
  (prod = .failed ∧ hol = .failed) ∨ (prod = .diverged ∧ hol = .diverged)

/-- Shared-memory operator relation. -/
def ShmemOpRel (prod : FfiShmemOp) (hol : HolShmemOp) : Prop :=
  (prod = .mappedRead ∧ hol = .mappedRead) ∨
    (prod = .mappedWrite ∧ hol = .mappedWrite)

/-- External-call name relation: production `String` via the byte codec. -/
def FfiNameRel : FfiName → HolFfiName → Prop
  | .extCall name, .extCall holName => holName = Flapjack.Basis.Pure.MlString.ofString name
  | .sharedMem operator, .sharedMem holOperator => ShmemOpRel operator holOperator
  | _, _ => False

/-- Oracle result relation. -/
def OracleResultRel {σ : Type} : FfiOracleResult σ → HolOracleResult σ → Prop
  | .returned state bytes, .ret holState holBytes => state = holState ∧ BytesRel bytes holBytes
  | .final outcome, .final holOutcome => OutcomeRel outcome holOutcome
  | _, _ => False

/-- I/O event relation. -/
def FfiEventRel (prod : FfiEvent) (hol : HolIoEvent) : Prop :=
  FfiNameRel prod.name hol.name ∧
    BytesRel prod.configuration hol.configuration ∧
    BytesPairRel prod.bytes hol.bytes

/-- Event-list relation (no dependency on `List.Forall₂`, which is absent here). -/
def FfiEventListRel : List FfiEvent → List HolIoEvent → Prop
  | [], [] => True
  | head :: tail, holHead :: holTail => FfiEventRel head holHead ∧ FfiEventListRel tail holTail
  | _, _ => False

/-- Final event relation. -/
def FfiFinalEventRel (prod : FfiFinalEvent) (hol : HolFinalEvent) : Prop :=
  FfiNameRel prod.name hol.name ∧
    BytesRel prod.configuration hol.configuration ∧
    BytesRel prod.bytes hol.bytes ∧
    OutcomeRel prod.outcome hol.outcome

/-- State relation: host state, observable events and the oracle function agree. -/
def FfiStateRel {σ : Type} (prod : FfiState σ) (hol : HolFfiState σ) : Prop :=
  hol.ffiState = prod.state ∧
    FfiEventListRel prod.ioEvents hol.ioEvents ∧
    ∀ (name : FfiName) (holName : HolFfiName), FfiNameRel name holName →
      ∀ (configuration : List UInt8) (holConfiguration : List (BitVec 8))
        (bytes : List UInt8) (holBytes : List (BitVec 8)),
        BytesRel configuration holConfiguration → BytesRel bytes holBytes →
        OracleResultRel (prod.oracle name prod.state configuration bytes)
          (hol.oracle holName hol.ffiState holConfiguration holBytes)

/-- Result relation. -/
def FfiResultRel {σ : Type} : FfiResult σ → HolFfiResult σ → Prop
  | .returned state bytes, .ret holState holBytes => FfiStateRel state holState ∧ BytesRel bytes holBytes
  | .final event, .final holEvent => FfiFinalEventRel event holEvent
  | _, _ => False

theorem ffiNameRel_empty_extCall :
    FfiNameRel (.extCall "") (.extCall (.implode [])) := by
  simp [FfiNameRel, Flapjack.Basis.Pure.MlString.ofString]

theorem callFFIHOL_empty_extCall (state : HolFfiState σ)
    (configuration bytes : List (BitVec 8)) :
    callFFIHOL state (.extCall (.implode [])) configuration bytes = .ret state bytes := by
  simp [callFFIHOL]

/-- The identity external call agrees in both representations. -/
theorem callFfi_empty_extCall_bridge {σ : Type} (state : FfiState σ) (holState : HolFfiState σ)
    (hrel : FfiStateRel state holState)
    (configuration bytes : List UInt8) :
    FfiResultRel (callFfi state (.extCall "") configuration bytes)
      (callFFIHOL holState (.extCall (.implode []))
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  rw [callFfi_empty_extCall, callFFIHOL_empty_extCall]
  exact ⟨hrel, bytesRel_map_byteToBits bytes⟩

end Flapjack