import Flapjack.FfiBridge

/-!
# Production `FfiState` / exact `HolFfiState` bridge regression

Kernel-checked fixtures pinning the untagged bridge in `Flapjack/FfiBridge.lean`:
the `UInt8` -> `BitVec 8` byte round trips, the byte-list relation, the empty
external-call name correspondence, a concrete `FfiStateRel` fixture whose oracle
corresponds bytewise, and the `callFfi`/`callFFIHOL` identity-call bridge.
-/

namespace Flapjack.Test.FfiBridgeParity

open Flapjack

/-- Byte round trip through the exact `BitVec 8` carrier. -/
example : bitsToByte (byteToBits (7 : UInt8)) = 7 := bitsToByte_byteToBits 7

/-- The `UInt8` value is preserved by the byte embedding. -/
example : (byteToBits (200 : UInt8)).toNat = 200 := byteToBits_toNat 200

/-- Related byte lists for the all-bytes embedding. -/
example : BytesRel [1, 2, 3] [byteToBits 1, byteToBits 2, byteToBits 3] :=
  bytesRel_map_byteToBits [1, 2, 3]

/-- The empty external-call name corresponds to the empty `MlString`. -/
example : FfiNameRel (FfiName.extCall "") (HolFfiName.extCall (.implode [])) :=
  ffiNameRel_empty_extCall

private def prodOracle : FfiOracle Nat :=
  fun _ state _ bytes => .returned (state + 1) (bytes ++ bytes)

private def holOracle : HolOracle Nat :=
  fun _ state _ bytes => .ret (state + 1) (bytes ++ bytes)

private def prodState : FfiState Nat :=
  { oracle := prodOracle, state := 0, ioEvents := [] }

private def holState : HolFfiState Nat :=
  { oracle := holOracle, ffiState := 0, ioEvents := [] }

/-- Concrete state relation: empty event lists and bytewise oracle correspondence. -/
theorem fixture_rel : FfiStateRel prodState holState := by
  refine ⟨rfl, ?_, ?_⟩
  · exact trivial
  · intro _name _holName _hname _state _configuration _holConfiguration bytes holBytes _hconf hbytes
    simp only [prodState, holState, prodOracle, holOracle, OracleResultRel, BytesRel] at hbytes ⊢
    rw [List.map_append, List.map_append, hbytes]
    exact ⟨trivial, rfl⟩

/-- The identity external call relates the two `call` implementations. -/
example : FfiResultRel (callFfi prodState (FfiName.extCall "") [1] [2])
    (callFFIHOL holState (HolFfiName.extCall (.implode []))
      ([1].map byteToBits) ([2].map byteToBits)) :=
  callFfi_empty_extCall_bridge prodState holState fixture_rel [1] [2]

private def prodFinalOracle : FfiOracle Nat := fun _ _ _ _ => .final .failed
private def holFinalOracle : HolOracle Nat := fun _ _ _ _ => .final .failed

private def prodFinalState : FfiState Nat :=
  { oracle := prodFinalOracle, state := 0, ioEvents := [] }

private def holFinalState : HolFfiState Nat :=
  { oracle := holFinalOracle, ffiState := 0, ioEvents := [] }

/-- A related pair of states whose oracle finalises with `failed`. -/
theorem finalState_rel : FfiStateRel prodFinalState holFinalState := by
  refine ⟨rfl, ?_, ?_⟩
  · exact trivial
  · intro _name _holName _hname _state _configuration _holConfiguration bytes holBytes _hconf _hbytes
    simp [prodFinalState, holFinalState, prodFinalOracle, holFinalOracle,
      OracleResultRel, OutcomeRel]

/-- A nonempty external call that the oracle finalises agrees. -/
example : FfiResultRel (callFfi prodFinalState (FfiName.extCall "f") [1] [2])
    (callFFIHOL holFinalState
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "f"))
      ([1].map byteToBits) ([2].map byteToBits)) :=
  callFfi_extCall_oracleFinal_bridge prodFinalState holFinalState finalState_rel "f"
    (by decide) (by decide) [1] [2] .failed rfl

/-- A nonempty external call whose returned length differs agrees. -/
example : FfiResultRel (callFfi prodState (FfiName.extCall "f") [1] [2])
    (callFFIHOL holState
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "f"))
      ([1].map byteToBits) ([2].map byteToBits)) :=
  callFfi_extCall_lengthFailure_bridge prodState holState fixture_rel "f"
    (by decide) (by decide) [1] [2] 1 [2, 2] rfl (by decide)



/-- A nonempty external call whose returned length matches agrees. -/
example : FfiResultRel (callFfi prodState (FfiName.extCall "f") [] [])
    (callFFIHOL holState
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "f")) [] []) :=
  callFfi_extCall_success_bridge prodState holState fixture_rel "f"
    (by decide) (by decide) [] [] 1 [] (by simp [prodState, prodOracle]) rfl

/-- A shared-memory call that the oracle finalises agrees. -/
example : FfiResultRel (callFfi prodFinalState (FfiName.sharedMem .mappedRead) [1] [2])
    (callFFIHOL holFinalState (HolFfiName.sharedMem .mappedRead)
      ([1].map byteToBits) ([2].map byteToBits)) :=
  callFfi_sharedMem_oracleFinal_bridge prodFinalState holFinalState finalState_rel
    .mappedRead .mappedRead (Or.inl ⟨rfl, rfl⟩) [1] [2] .failed rfl

/-- A shared-memory call whose returned length differs agrees. -/
example : FfiResultRel (callFfi prodState (FfiName.sharedMem .mappedWrite) [1] [2])
    (callFFIHOL holState (HolFfiName.sharedMem .mappedWrite)
      ([1].map byteToBits) ([2].map byteToBits)) :=
  callFfi_sharedMem_lengthFailure_bridge prodState holState fixture_rel
    .mappedWrite .mappedWrite (Or.inr ⟨rfl, rfl⟩) [1] [2] 1 [2, 2] rfl (by decide)

/-- A shared-memory call whose returned length matches agrees. -/
example : FfiResultRel (callFfi prodState (FfiName.sharedMem .mappedRead) [] [])
    (callFFIHOL holState (HolFfiName.sharedMem .mappedRead) [] []) :=
  callFfi_sharedMem_success_bridge prodState holState fixture_rel
    .mappedRead .mappedRead (Or.inl ⟨rfl, rfl⟩) [] [] 1 []
    (by simp [prodState, prodOracle]) rfl

example : BytesPairRel ([(1 : UInt8), 2].zip [(3 : UInt8)])
    ([byteToBits 1, byteToBits 2].zip [byteToBits 3]) :=
  bytesPairRel_zip (bytesRel_map_byteToBits [1, 2]) (bytesRel_map_byteToBits [3])

example : FfiEventListRel ([] ++ []) ([] ++ []) :=
  ffiEventListRel_append (by trivial) (by trivial)

/-- Host-only oracle that returns the requested bytes unchanged. -/
private def prodEchoOracle : FfiOracle Nat := fun _ state _ bytes => .returned (state + 1) bytes
private def holEchoOracle : HolOracle Nat := fun _ state _ bytes => .ret (state + 1) bytes

private def prodEchoState : FfiState Nat :=
  { oracle := prodEchoOracle, state := 0, ioEvents := [] }

private def holEchoState : HolFfiState Nat :=
  { oracle := holEchoOracle, ffiState := 0, ioEvents := [] }

/-- The echo pair satisfies the persistent state relation. -/
theorem echoState_rel : FfiStateRel prodEchoState holEchoState := by
  refine ⟨rfl, ?_, ?_⟩
  · exact trivial
  · intro _name _holName _hname _state _configuration _holConfiguration bytes holBytes _hconf hbytes
    simp only [prodEchoState, holEchoState, prodEchoOracle, holEchoOracle]
    exact ⟨rfl, hbytes⟩

/-- Projection helpers mirroring the HOL `call_shmem_ok_*` oracle rows. -/
private def shmemHost : Nat :=
  match callFFIHOL holEchoState (HolFfiName.sharedMem .mappedRead)
      ([7, 8].map byteToBits) ([1].map byteToBits) with
  | .ret st _ => st.ffiState
  | .final _ => 99

private def shmemEvents : Nat :=
  match callFFIHOL holEchoState (HolFfiName.sharedMem .mappedRead)
      ([7, 8].map byteToBits) ([1].map byteToBits) with
  | .ret st _ => st.ioEvents.length
  | .final _ => 0

private def shmemBytes : Nat :=
  match callFFIHOL holEchoState (HolFfiName.sharedMem .mappedRead)
      ([7, 8].map byteToBits) ([1].map byteToBits) with
  | .ret _ bs => bs.length
  | .final _ => 0

/-- `call_shmem_ok_host`: the shared-memory call advances the host state. -/
example : shmemHost = 1 := by simp [shmemHost, callFFIHOL, holEchoState, holEchoOracle]

/-- `call_shmem_ok_events`: the shared-memory call appends one event. -/
example : shmemEvents = 1 := by simp [shmemEvents, callFFIHOL, holEchoState, holEchoOracle]

/-- `call_shmem_ok_bytes`: the returned byte list is the oracle output. -/
example : shmemBytes = 1 := by simp [shmemBytes, callFFIHOL, holEchoState, holEchoOracle]

/-- Direct HOL `call_shmem_length_failure` oracle row from
    `ffi_state_carrier_probe.out`: a doubled byte result becomes FFI_failed. -/
example : callFFIHOL holState (HolFfiName.sharedMem .mappedWrite)
    ([7, 8].map byteToBits) ([1].map byteToBits) =
    HolFfiResult.final
      (HolFinalEvent.mk (HolFfiName.sharedMem HolShmemOp.mappedWrite)
        ([7, 8].map byteToBits) ([1].map byteToBits) .failed) := by
  simp [callFFIHOL, holState, holOracle]

private def holDivergedOracle : HolOracle Nat := fun _ _ _ _ => .final .diverged

private def holDivergedState : HolFfiState Nat :=
  { oracle := holDivergedOracle, ffiState := 0, ioEvents := [] }

/-- Direct HOL `call_shmem_final_event` oracle row from
    `ffi_state_carrier_probe.out`: a terminal oracle preserves FFI_diverged. -/
example : callFFIHOL holDivergedState (HolFfiName.sharedMem .mappedRead)
    ([7, 8].map byteToBits) ([1].map byteToBits) =
    HolFfiResult.final
      (HolFinalEvent.mk (HolFfiName.sharedMem HolShmemOp.mappedRead)
        ([7, 8].map byteToBits) ([1].map byteToBits) .diverged) := by
  simp [callFFIHOL, holDivergedState, holDivergedOracle]

/-- The shared-memory echo bridge holds for the same call. -/
example : FfiResultRel (callFfi prodEchoState (FfiName.sharedMem .mappedRead)
      [(7 : UInt8), 8] [(1 : UInt8)])
    (callFFIHOL holEchoState (HolFfiName.sharedMem .mappedRead)
      ([7, 8].map byteToBits) ([1].map byteToBits)) :=
  callFfi_sharedMem_success_bridge prodEchoState holEchoState echoState_rel
    .mappedRead .mappedRead (Or.inl ⟨rfl, rfl⟩) [(7 : UInt8), 8]
    [(1 : UInt8)] 1 [(1 : UInt8)] rfl rfl

/-! ## Direct byte-boundary fixtures for the executed `ExtCall` name (flapjack-0up.2)

HOL-EVAL rows `oracle_return` / `extcall_name_explode` / `extcall_name_len` in
`scripts/hol-probes/ffi_call_probe.out` pin the external-call event name to
`ExtCall «foo»` with `explode «foo» = "foo"` and `strlen «foo» = 3`.  The fixtures
below pin the production-side byte boundary: a byte-ranged `String` name maps to
its `ofString` image with identical character codes. -/

/-- The concrete `foo` name is byte-ranged (`f`, `o` = 102, 111 < 256). -/
example : FfiNameByteRanged (FfiName.extCall "foo") := by
  intro c hc
  simp at hc
  rcases hc with rfl | rfl | rfl <;> decide

/-- The byte-boundary witness for `foo`: related name and explicit codes. -/
example : FfiNameRel (FfiName.extCall "foo")
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "foo")) ∧
    (Flapjack.Basis.Pure.MlString.ofString "foo").explode.map BitVec.toNat =
      [102, 111, 111] := by
  have h := ffiNameRel_extCall_byteBoundary (name := "foo") (by decide)
  exact ⟨h.1, by decide⟩

/-- The byte-boundary witness reaches the event boundary for the `foo` call. -/
example : FfiEventRel
    { name := FfiName.extCall "foo", configuration := [(1 : UInt8), 2],
      bytes := [((3 : UInt8), 5), (4, 6)] }
    { name := HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "foo"),
      configuration := [byteToBits 1, byteToBits 2],
      bytes := [(byteToBits 3, byteToBits 5), (byteToBits 4, byteToBits 6)] } :=
  ffiEventRel_extCall_byteBoundary "foo" (by decide)
    [1, 2] [byteToBits 1, byteToBits 2] [(3, 5), (4, 6)]
    [(byteToBits 3, byteToBits 5), (byteToBits 4, byteToBits 6)]
    (bytesRel_map_byteToBits [1, 2])
    (bytesPairRel_zip (bytesRel_map_byteToBits [3, 4]) (bytesRel_map_byteToBits [5, 6]))

/-- The byte-ranged `success` boundary combines the name witness with the exact
    `callFfi` event append. -/
example : FfiNameRel (FfiName.extCall "foo")
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "foo")) ∧
    callFfi prodEchoState (FfiName.extCall "foo") [1] [2] =
      FfiResult.returned
        { prodEchoState with
            state := 0 + 1
            ioEvents := prodEchoState.ioEvents ++
              [{ name := FfiName.extCall "foo", configuration := [1],
                 bytes := [(2, 2)] }] } [2] := by
  refine ⟨(ffiNameRel_extCall_byteBoundary (name := "foo") (by decide)).1, ?_⟩
  have h := callFfi_extCall_success prodEchoState "foo" (by decide)
    [1] [2] (0 + 1) [2] (by simp [prodEchoState, prodEchoOracle]) (by simp)
  simpa [prodEchoState, prodEchoOracle] using h

/-! ## Production `ProgByteRanged` name boundary (flapjack-0up.2.1)

The byte-rangedness premise is exactly the `ExtCall` clause of the production
`PanLang.ProgByteRanged` predicate, not an unconditional claim about arbitrary
`String`s. -/

/-- A `ProgByteRanged` `ExtCall` node has a byte-ranged name. -/
example : FfiNameByteRanged (FfiName.extCall "foo") :=
  ffiNameByteRanged_extCall_of_progByteRanged (width := 64) "foo" (.const 0) (.const 0) (.const 0) (.const 0)
    ⟨by decide, trivial, trivial, trivial, trivial⟩

/-- The `ProgByteRanged` premise feeds the executed event-name boundary. -/
example : FfiNameRel (FfiName.extCall "foo")
      (HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "foo")) ∧
    callFfi prodEchoState (FfiName.extCall "foo") [1] [2] =
      FfiResult.returned
        { prodEchoState with
            state := 0 + 1
            ioEvents := prodEchoState.ioEvents ++
              [{ name := FfiName.extCall "foo", configuration := [1],
                 bytes := [(2, 2)] }] } [2] := by
  have hprog : Flapjack.Pancake.PanLang.ProgByteRanged
      (Flapjack.Prog.extCall "foo" (.const 0) (.const 0) (.const 0) (.const 0) :
        Flapjack.Prog (BitVec 64)) :=
    ⟨by decide, trivial, trivial, trivial, trivial⟩
  refine ⟨(ffiNameRel_extCall_byteBoundary (name := "foo") (by decide)).1, ?_⟩
  have h := callFfi_extCall_success_eventNameBoundary_of_progByteRanged
    prodEchoState "foo" (.const 0) (.const 0) (.const 0) (.const 0) hprog (by decide)
    [1] [2] (0 + 1) [2] (by simp [prodEchoState, prodEchoOracle]) (by simp)
  simpa [prodEchoState, prodEchoOracle] using h.2.2

def runChecks : IO Bool := do

  IO.println "PASS production FfiState / exact HolFfiState bridge fixtures (identity, final, length failure, success, shared-mem, shared-mem HOL rows, append/zip)"
  IO.println "PASS ExtCall FFI-name byte boundary witness (flapjack-0up.2)"
  IO.println "PASS production ProgByteRanged ExtCall name boundary (flapjack-0up.2.1)"
  pure true

end Flapjack.Test.FfiBridgeParity
