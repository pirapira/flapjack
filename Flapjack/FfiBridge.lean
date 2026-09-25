import Flapjack.Ffi
import Flapjack.FfiHOL
import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Prog

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

/-- Persistent oracle correspondence, quantified over every pair of paired host states. -/
def OracleRel {σ : Type} (prod : FfiOracle σ) (hol : HolOracle σ) : Prop :=
  ∀ (name : FfiName) (holName : HolFfiName), FfiNameRel name holName →
    ∀ (state : σ) (configuration : List UInt8) (holConfiguration : List (BitVec 8))
      (bytes : List UInt8) (holBytes : List (BitVec 8)),
      BytesRel configuration holConfiguration → BytesRel bytes holBytes →
      OracleResultRel (prod name state configuration bytes)
        (hol holName state holConfiguration holBytes)

/-- State relation: host state, observable events and a persistent oracle correspondence. -/
def FfiStateRel {σ : Type} (prod : FfiState σ) (hol : HolFfiState σ) : Prop :=
  hol.ffiState = prod.state ∧
    FfiEventListRel prod.ioEvents hol.ioEvents ∧
    OracleRel prod.oracle hol.oracle

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
    rfl state.state configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
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
    rfl state.state configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
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

/-- Under `FfiStateRel`, a nonempty external call with a matching return length agrees. -/
theorem callFfi_extCall_success_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState) (name : String)
    (hr : ∀ c ∈ name.toList, c.toNat < 256) (hne : name ≠ "")
    (configuration bytes : List UInt8) (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.extCall name) state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    FfiResultRel (callFfi state (.extCall name) configuration bytes)
      (callFFIHOL holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString name) =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    simpa only [HolFfiName.extCall.injEq] using holName_ne_empty_of_ne hne hr
  rw [callFfi_extCall_success state name hne configuration bytes nextState nextBytes ho hlen]
  have hcorr := hrel.2.2 (.extCall name) (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    rfl state.state configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
  simp only [OracleResultRel] at hcorr
  cases holRes with
  | final holOutcome => exact hcorr.elim
  | ret holState' holBytes' =>
      obtain ⟨hstate, hbytes⟩ := hcorr
      have hlenH : holBytes'.length = (bytes.map byteToBits).length := by
        have hlen' := congrArg List.length hbytes
        simp only [List.length_map] at hlen'
        rw [hlen', hlen]
        simp
      rw [callFFIHOL_ret holState (.extCall (Flapjack.Basis.Pure.MlString.ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits) holState' holBytes' hneH hy]
      rw [if_pos hlenH]
      refine ⟨⟨hstate.symm, ?_, hrel.2.2⟩, hbytes⟩
      exact ffiEventListRel_append hrel.2.1
        ⟨⟨rfl, bytesRel_map_byteToBits configuration,
          bytesPairRel_zip (bytesRel_map_byteToBits bytes) hbytes⟩, trivial⟩


/-- Production `callFfi` on any call other than the empty external call, finalised. -/
theorem callFfi_nonextCall_final {σ : Type} (state : FfiState σ) (name : FfiName)
    (hname : name ≠ .extCall "") (configuration bytes : List UInt8) (outcome : FfiOutcome)
    (ho : state.oracle name state.state configuration bytes = .final outcome) :
    callFfi state name configuration bytes =
      .final { name := name, configuration := configuration, bytes := bytes,
               outcome := outcome } := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h hname
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

/-- Production `callFfi` on any nonempty call whose oracle returns the wrong length. -/
theorem callFfi_nonextCall_return_lengthFailure {σ : Type} (state : FfiState σ) (name : FfiName)
    (hname : name ≠ .extCall "") (configuration bytes : List UInt8) (nextState : σ)
    (nextBytes : List UInt8)
    (ho : state.oracle name state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length ≠ bytes.length) :
    callFfi state name configuration bytes =
      .final { name := name, configuration := configuration, bytes := bytes,
               outcome := .failed } := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h hname
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

/-- Production `callFfi` on any nonempty call whose oracle returns a matching length. -/
theorem callFfi_nonextCall_success {σ : Type} (state : FfiState σ) (name : FfiName)
    (hname : name ≠ .extCall "") (configuration bytes : List UInt8) (nextState : σ)
    (nextBytes : List UInt8)
    (ho : state.oracle name state.state configuration bytes = .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    callFfi state name configuration bytes =
      .returned { state with
          state := nextState
          ioEvents := state.ioEvents ++
            [{ name := name, configuration := configuration,
               bytes := bytes.zip nextBytes }] } nextBytes := by
  unfold callFfi
  split
  · rename_i h
    exact absurd h hname
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

/-- Under `FfiStateRel`, a shared-memory call that the oracle finalises agrees. -/
theorem callFfi_sharedMem_oracleFinal_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState)
    (operator : FfiShmemOp) (holOperator : HolShmemOp) (hop : ShmemOpRel operator holOperator)
    (configuration bytes : List UInt8) (outcome : FfiOutcome)
    (ho : state.oracle (.sharedMem operator) state.state configuration bytes = .final outcome) :
    FfiResultRel (callFfi state (.sharedMem operator) configuration bytes)
      (callFFIHOL holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.sharedMem holOperator =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    intro h
    cases h
  rw [callFfi_nonextCall_final state (.sharedMem operator) (by intro h; cases h) configuration
    bytes outcome ho]
  have hcorr := hrel.2.2 (.sharedMem operator) (.sharedMem holOperator) hop state.state
    configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.sharedMem holOperator)
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
  simp only [OracleResultRel] at hcorr
  cases holRes with
  | final holOutcome =>
      rw [callFFIHOL_final holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits) holOutcome hneH hy]
      exact ⟨hop, bytesRel_map_byteToBits configuration, bytesRel_map_byteToBits bytes, hcorr⟩
  | ret holState' holBytes' => exact hcorr.elim

/-- Under `FfiStateRel`, a shared-memory call with a mismatched return length agrees. -/
theorem callFfi_sharedMem_lengthFailure_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState)
    (operator : FfiShmemOp) (holOperator : HolShmemOp) (hop : ShmemOpRel operator holOperator)
    (configuration bytes : List UInt8) (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.sharedMem operator) state.state configuration bytes
      = .returned nextState nextBytes)
    (hlen : nextBytes.length ≠ bytes.length) :
    FfiResultRel (callFfi state (.sharedMem operator) configuration bytes)
      (callFFIHOL holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.sharedMem holOperator =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    intro h
    cases h
  rw [callFfi_nonextCall_return_lengthFailure state (.sharedMem operator)
    (by intro h; cases h) configuration bytes nextState nextBytes ho hlen]
  have hcorr := hrel.2.2 (.sharedMem operator) (.sharedMem holOperator) hop state.state
    configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.sharedMem holOperator)
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
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
      rw [callFFIHOL_ret holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits) holState' holBytes' hneH hy]
      rw [if_neg hlenH]
      exact ⟨hop, bytesRel_map_byteToBits configuration, bytesRel_map_byteToBits bytes,
        Or.inl ⟨rfl, rfl⟩⟩

/-- Under `FfiStateRel`, a shared-memory call with a matching return length agrees. -/
theorem callFfi_sharedMem_success_bridge {σ : Type} (state : FfiState σ)
    (holState : HolFfiState σ) (hrel : FfiStateRel state holState)
    (operator : FfiShmemOp) (holOperator : HolShmemOp) (hop : ShmemOpRel operator holOperator)
    (configuration bytes : List UInt8) (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.sharedMem operator) state.state configuration bytes
      = .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    FfiResultRel (callFfi state (.sharedMem operator) configuration bytes)
      (callFFIHOL holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  have hneH : ¬ (HolFfiName.sharedMem holOperator =
      HolFfiName.extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])) := by
    intro h
    cases h
  rw [callFfi_nonextCall_success state (.sharedMem operator) (by intro h; cases h) configuration
    bytes nextState nextBytes ho hlen]
  have hcorr := hrel.2.2 (.sharedMem operator) (.sharedMem holOperator) hop state.state
    configuration (configuration.map byteToBits) bytes (bytes.map byteToBits)
    (bytesRel_map_byteToBits configuration) (bytesRel_map_byteToBits bytes)
  rw [ho] at hcorr
  generalize hy : holState.oracle (.sharedMem holOperator)
    state.state (configuration.map byteToBits) (bytes.map byteToBits) = holRes at hcorr
  rw [← hrel.1] at hy
  simp only [OracleResultRel] at hcorr
  cases holRes with
  | final holOutcome => exact hcorr.elim
  | ret holState' holBytes' =>
      obtain ⟨hstate, hbytes⟩ := hcorr
      have hlenH : holBytes'.length = (bytes.map byteToBits).length := by
        have hlen' := congrArg List.length hbytes
        simp only [List.length_map] at hlen'
        rw [hlen', hlen]
        simp
      rw [callFFIHOL_ret holState (.sharedMem holOperator)
        (configuration.map byteToBits) (bytes.map byteToBits) holState' holBytes' hneH hy]
      rw [if_pos hlenH]
      refine ⟨⟨hstate.symm, ?_, hrel.2.2⟩, hbytes⟩
      exact ffiEventListRel_append hrel.2.1
        ⟨⟨hop, bytesRel_map_byteToBits configuration,
          bytesPairRel_zip (bytesRel_map_byteToBits bytes) hbytes⟩, trivial⟩

/-! ## Byte-boundary witness for the executed `ExtCall` name path (flapjack-0up.2)

HOL `call_FFI` (`cakeml/semantics/ffi/ffiScript.sml:45-79`) receives the external
call name as an `mlstring`, whereas production `FfiName.extCall` stores a Lean
`String` (`Flapjack/Ffi.lean`).  The bridge `FfiNameRel` already identifies a
production name with its `ofString` image; the theorems below record the extra
*byte-boundary* witness: when every character of the production `String` has a
code point below `256`, the HOL image has exactly the same character codes, so no
information is lost or truncated at the `mlstring` boundary.  This is the
production-side half of `flapjack-0up`; the parser-to-FFI precondition that a
parsed program's `ExtCall` names satisfy `∀ c ∈ name.toList, c.toNat < 256` is
tracked separately by `flapjack-0up.1` / `flapjack-an4`. -/

/-- A production FFI name whose `ExtCall` payload is byte-ranged (every character
    has a code point below `256`).  `sharedMem` operators carry no name bytes. -/
def FfiNameByteRanged : FfiName → Prop
  | .extCall name => ∀ c ∈ name.toList, c.toNat < 256
  | .sharedMem _ => True

/-- The byte-boundary witness: a byte-ranged production `ExtCall` name is exactly
    its `ofString` HOL image, character code for character code. -/
theorem ffiNameRel_extCall_byteBoundary {name : String}
    (hr : ∀ c ∈ name.toList, c.toNat < 256) :
    FfiNameRel (.extCall name)
        (.extCall (Flapjack.Basis.Pure.MlString.ofString name)) ∧
      (Flapjack.Basis.Pure.MlString.ofString name).explode.map BitVec.toNat =
        name.toList.map (fun c => c.toNat) := by
  refine ⟨rfl, ?_⟩
  rw [Flapjack.Basis.Pure.MlString.explode_map_toNat_ofString]
  apply List.map_congr_left
  intro c hc
  exact Nat.mod_eq_of_lt (hr c hc)

/-- A byte-ranged production `ExtCall` event relates to the HOL event with the
    same `ofString` name. -/
theorem ffiEventRel_extCall_byteBoundary (name : String)
    (hr : ∀ c ∈ name.toList, c.toNat < 256)
    (configuration : List UInt8) (holConfiguration : List (BitVec 8))
    (bytes : List (UInt8 × UInt8)) (holBytes : List (BitVec 8 × BitVec 8))
    (hconf : BytesRel configuration holConfiguration) (hb : BytesPairRel bytes holBytes) :
    FfiEventRel
      { name := .extCall name, configuration := configuration, bytes := bytes }
      { name := .extCall (Flapjack.Basis.Pure.MlString.ofString name),
        configuration := holConfiguration, bytes := holBytes } :=
  ⟨(ffiNameRel_extCall_byteBoundary hr).1, hconf, hb⟩

/-- Production `callFfi` appends an event whose name reaches the HOL boundary
    (`ofString`) when the input name is byte-ranged. -/
theorem callFfi_extCall_success_eventNameBoundary {σ : Type} (state : FfiState σ)
    (name : String) (hne : name ≠ "") (hr : ∀ c ∈ name.toList, c.toNat < 256)
    (configuration bytes : List UInt8) (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.extCall name) state.state configuration bytes =
      .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    FfiNameRel (.extCall name) (.extCall (Flapjack.Basis.Pure.MlString.ofString name)) ∧
      (Flapjack.Basis.Pure.MlString.ofString name).explode.map BitVec.toNat =
        name.toList.map (fun c => c.toNat) ∧
      callFfi state (.extCall name) configuration bytes =
        .returned { state with
            state := nextState
            ioEvents := state.ioEvents ++
              [{ name := .extCall name, configuration := configuration,
                 bytes := bytes.zip nextBytes }] } nextBytes :=
  ⟨(ffiNameRel_extCall_byteBoundary hr).1, (ffiNameRel_extCall_byteBoundary hr).2,
    callFfi_extCall_success state name hne configuration bytes nextState nextBytes ho hlen⟩

/-! ## Connecting the executed `ProgByteRanged` premise to the FFI event bytes
    (flapjack-0up.2.1)

The byte-level premise above is not unconditional: it is exactly the
`NameRanged` requirement that the production `PanLang.ProgByteRanged` predicate
imposes on the `ExtCall` function name (`Flapjack/Pancake/PanLang/Prog.lean`).
The following theorems take that production premise, rather than an arbitrary
String, as the hypothesis. -/

/-- The executed `ExtCall` name is byte-ranged exactly when the production name
    satisfies `PanLang.NameRanged`. -/
theorem ffiNameByteRanged_extCall_iff_nameRanged (name : String) :
    FfiNameByteRanged (.extCall name) ↔ Flapjack.Pancake.PanLang.NameRanged name :=
  Iff.rfl

/-- A production program whose `ExtCall` node is `ProgByteRanged` has a
    byte-ranged FFI name. -/
theorem ffiNameByteRanged_extCall_of_progByteRanged {width : Nat}
    (function : String) (configuration configurationLength array arrayLength : Exp (BitVec width))
    (hprog : Flapjack.Pancake.PanLang.ProgByteRanged
      (.extCall function configuration configurationLength array arrayLength)) :
    FfiNameByteRanged (.extCall function) :=
  hprog.1

/-- The executed `callFfi` `ExtCall` success event name is the exact `mlstring`
    encoding of a `ProgByteRanged` function name, connecting the production
    byte-rangedness premise to the appended `ioEvents` entry. -/
theorem callFfi_extCall_success_eventNameBoundary_of_progByteRanged {width : Nat} {σ : Type}
    (state : FfiState σ) (function : String)
    (configuration configurationLength array arrayLength : Exp (BitVec width))
    (hprog : Flapjack.Pancake.PanLang.ProgByteRanged
      (.extCall function configuration configurationLength array arrayLength))
    (hne : function ≠ "") (configurationBytes bytes : List UInt8)
    (nextState : σ) (nextBytes : List UInt8)
    (ho : state.oracle (.extCall function) state.state configurationBytes bytes =
      .returned nextState nextBytes)
    (hlen : nextBytes.length = bytes.length) :
    FfiNameRel (.extCall function) (.extCall (Flapjack.Basis.Pure.MlString.ofString function)) ∧
      (Flapjack.Basis.Pure.MlString.ofString function).explode.map BitVec.toNat =
        function.toList.map (fun c => c.toNat) ∧
      callFfi state (.extCall function) configurationBytes bytes =
        .returned { state with
            state := nextState
            ioEvents := state.ioEvents ++
              [{ name := .extCall function, configuration := configurationBytes,
                 bytes := bytes.zip nextBytes }] } nextBytes :=
  callFfi_extCall_success_eventNameBoundary state function hne hprog.1 configurationBytes bytes
    nextState nextBytes ho hlen

end Flapjack
