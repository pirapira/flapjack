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


/-- A nonempty byte-ranged `String` maps to a nonempty `mlstring`. -/
theorem holName_ne_empty_of_ne {name : String}
    (hne : name ≠ "") (hr : ∀ c ∈ name.toList, c.toNat < 256) :
    Flapjack.Basis.Pure.MlString.ofString name ≠
      (Flapjack.Basis.Pure.MlString.MlString.implode [] :
        Flapjack.Basis.Pure.MlString.MlString) := by
  intro h
  have h1 := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hr] at h1
  have h2 : Flapjack.Basis.Pure.MlString.toStringOfBytes
      (Flapjack.Basis.Pure.MlString.MlString.implode []) = "" := rfl
  rw [h2] at h1
  exact hne h1

/-- Production `callFfi` on a nonempty external call whose oracle finalises. -/
theorem callFfi_extCall_final {σ : Type} (state : FfiState σ) (name : String)
    (hne : name ≠ "") (configuration bytes : List UInt8) (outcome : FfiOutcome)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .final outcome) :
    callFfi state (.extCall name) configuration bytes =
      .final { name := .extCall name, configuration := configuration, bytes := bytes,
               outcome := outcome } := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h (by simpa only [FfiName.extCall.injEq] using hne)
  · split
    · rename_i nextState nextBytes hres
      have hc : FfiOracleResult.returned nextState nextBytes = FfiOracleResult.final outcome :=
        hres.symm.trans ho
      exact absurd hc (by simp)
    · rename_i holOutcome hres
      have hc : FfiOracleResult.final holOutcome = FfiOracleResult.final outcome :=
        hres.symm.trans ho
      injection hc with hoo
      subst hoo
      rfl

/-- Production `callFfi` on a nonempty external call whose oracle returns the wrong length. -/
theorem callFfi_extCall_return_lengthFailure {σ : Type} (state : FfiState σ) (name : String)
    (hne : name ≠ "") (configuration bytes : List UInt8) (nextState : σ)
    (nextBytes : List UInt8)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length ≠ bytes.length) :
    callFfi state (.extCall name) configuration bytes =
      .final { name := .extCall name, configuration := configuration, bytes := bytes,
               outcome := .failed } := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h (by simpa only [FfiName.extCall.injEq] using hne)
  · split
    · rename_i ns nb hres
      have hc : FfiOracleResult.returned ns nb = FfiOracleResult.returned nextState nextBytes :=
        hres.symm.trans ho
      injection hc with hns hnb
      subst hns
      subst hnb
      rw [if_neg (by simpa using hlen)]
    · rename_i holOutcome hres
      have hc : FfiOracleResult.final holOutcome = FfiOracleResult.returned nextState nextBytes :=
        hres.symm.trans ho
      exact absurd hc (by simp)

/-- Production `callFfi` on a nonempty external call whose oracle returns a matching length. -/
theorem callFfi_extCall_success {σ : Type} (state : FfiState σ) (name : String)
    (hne : name ≠ "") (configuration bytes : List UInt8) (nextState : σ)
    (nextBytes : List UInt8)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    callFfi state (.extCall name) configuration bytes =
      .returned { state with
          state := nextState
          ioEvents := state.ioEvents ++
            [{ name := .extCall name, configuration := configuration,
               bytes := bytes.zip nextBytes }] } nextBytes := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h (by simpa only [FfiName.extCall.injEq] using hne)
  · split
    · rename_i ns nb hres
      have hc : FfiOracleResult.returned ns nb = FfiOracleResult.returned nextState nextBytes :=
        hres.symm.trans ho
      injection hc with hns hnb
      subst hns
      subst hnb
      rw [if_pos (by simpa using hlen)]
    · rename_i holOutcome hres
      have hc : FfiOracleResult.final holOutcome = FfiOracleResult.returned nextState nextBytes :=
        hres.symm.trans ho
      exact absurd hc (by simp)

/-- Under `FfiStateRel`, a nonempty external call that the oracle finalises agrees. -/
theorem callFfi_extCall_oracleFinal_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState) (name : String)
    (hr : ∀ c ∈ name.toList, c.toNat < 256) (hne : name ≠ "")
    (configuration bytes : List UInt8) (outcome : FfiOutcome)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .final outcome) :
    FfiResultRel (callFfi state (.extCall name) configuration bytes)
      (callFFIHOL holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString name) =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    simpa only [HolFfiName.extCall.injEq] using holName_ne_empty_of_ne hne hr
  rw [callFfi_extCall_final state name hne configuration bytes outcome ho]
  have hcorr := hrel.2.2 (.extCall name) (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    rfl configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    holState.ffiState (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  simp only [OracleResultRel] at hcorr
  cases holRes with
  | final holOutcome =>
      rw [callFFIHOL_final holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits) holOutcome hneH hy]
      exact ⟨rfl, bytesRel_map_byteToBits configuration, bytesRel_map_byteToBits bytes, hcorr⟩
  | ret holState' holBytes' => exact hcorr.elim

/-- Under `FfiStateRel`, a nonempty external call with a mismatched return length agrees. -/
theorem callFfi_extCall_lengthFailure_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState) (name : String)
    (hr : ∀ c ∈ name.toList, c.toNat < 256) (hne : name ≠ "")
    (configuration bytes : List UInt8) (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length ≠ bytes.length) :
    FfiResultRel (callFfi state (.extCall name) configuration bytes)
      (callFFIHOL holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString name) =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    simpa only [HolFfiName.extCall.injEq] using holName_ne_empty_of_ne hne hr
  rw [callFfi_extCall_return_lengthFailure state name hne configuration bytes nextState nextBytes ho hlen]
  have hcorr := hrel.2.2 (.extCall name) (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    rfl configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    holState.ffiState (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  simp only [OracleResultRel] at hcorr
  cases holRes with
  | final holOutcome => exact hcorr.elim
  | ret holState' holBytes' =>
      obtain ⟨_, hbytes⟩ := hcorr
      have hlenH : holBytes'.length ≠ (bytes.map byteToBits).length := by
        intro hEq
        have hlenEq : holBytes'.length = nextBytes.length := by
          have := congrArg List.length hbytes
          simpa [BytesRel, List.length_map] using this
        exact hlen (by rw [← hlenEq, hEq]; simp)
      rw [callFFIHOL_ret holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits) holState' holBytes' hneH hy]
      rw [if_neg hlenH]
      exact ⟨rfl, bytesRel_map_byteToBits configuration, bytesRel_map_byteToBits bytes,
        Or.inl ⟨rfl, rfl⟩⟩


/-- Zipping two lists commutes with componentwise mapping. -/
theorem listMapZipPair {α β γ δ : Type} (f : α → γ) (g : β → δ) (l₁ : List α)
    (l₂ : List β) :
    (l₁.zip l₂).map (fun p => (f p.1, g p.2)) = (l₁.map f).zip (l₂.map g) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> rfl
  | cons a t ih =>
      cases l₂ with
      | nil => rfl
      | cons b u =>
          simp only [List.zip_cons_cons, List.map_cons]
          rw [ih u]

/-- The byte-pair relation commutes with pairing production and exact byte lists. -/
theorem bytesPairRel_zip {as bs : List UInt8} {as' bs' : List (BitVec 8)}
    (ha : BytesRel as as') (hb : BytesRel bs bs') :
    BytesPairRel (as.zip bs) (as'.zip bs') := by
  have ha' : as'.map BitVec.toNat = as.map UInt8.toNat := ha
  have hb' : bs'.map BitVec.toNat = bs.map UInt8.toNat := hb
  simp only [BytesPairRel]
  rw [listMapZipPair (f := BitVec.toNat) (g := BitVec.toNat),
    listMapZipPair (f := UInt8.toNat) (g := UInt8.toNat), ha', hb']

/-- The gradual event-list relation is preserved by list concatenation. -/
theorem ffiEventListRel_append {l1 l2 : List FfiEvent} {m1 m2 : List HolIoEvent}
    (h1 : FfiEventListRel l1 m1) (h2 : FfiEventListRel l2 m2) :
    FfiEventListRel (l1 ++ l2) (m1 ++ m2) := by
  induction l1 generalizing m1 with
  | nil =>
      cases m1 with
      | nil => simpa [FfiEventListRel] using h2
      | cons e es => exact (h1 : False).elim
  | cons e es ih =>
      cases m1 with
      | nil => exact (h1 : False).elim
      | cons e' es' => exact ⟨h1.1, ih h1.2⟩

end Flapjack
