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
  · intro _name _holName _hname _configuration _holConfiguration bytes holBytes _hconf hbytes
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
  · intro _name _holName _hname _configuration _holConfiguration bytes holBytes _hconf _hbytes
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



example : BytesPairRel ([(1 : UInt8), 2].zip [(3 : UInt8)])
    ([byteToBits 1, byteToBits 2].zip [byteToBits 3]) :=
  bytesPairRel_zip (bytesRel_map_byteToBits [1, 2]) (bytesRel_map_byteToBits [3])

example : FfiEventListRel ([] ++ []) ([] ++ []) :=
  ffiEventListRel_append (by trivial) (by trivial)

def runChecks : IO Bool := do
  IO.println "PASS production FfiState / exact HolFfiState bridge fixtures (identity, final, length failure, append/zip)"
  pure true

end Flapjack.Test.FfiBridgeParity
