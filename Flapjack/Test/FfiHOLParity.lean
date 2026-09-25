import Flapjack.FfiHOL

/-!
# FFI carrier parity

Pins the exact HOL `cakeml/semantics/ffi/ffiScript.sml` carrier shapes and the
`call_FFI` cases against the direct HOL oracle
`scripts/hol-probes/ffi_state_carrier_probe.out`.
-/

namespace Flapjack.Test.FfiHOLParity

open Flapjack

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

/-- Oracle that advances the host state by one and returns the input bytes. -/
private def osucc : HolOracle Nat :=
  fun _name state _configuration bytes => .ret (state + 1) bytes

/-- Oracle that returns twice the input bytes (a length failure). -/
private def obad : HolOracle Nat :=
  fun _name state _configuration bytes => .ret state (bytes ++ bytes)

/-- Oracle that diverges. -/
private def ofin : HolOracle Nat :=
  fun _name _state _configuration _bytes => .final .diverged

/-- The initial state using `osucc` at host state `0`. -/
private def st : HolFfiState Nat := initialHolFfiState osucc 0

/-- A non-empty external-call name. -/
private def nameOf : HolFfiName := .extCall (.implode [w8 102])

private def conf : List W := [w8 7, w8 8]

private def one : List W := [w8 1]

private def isDiverged : HolOracleResult Nat → Bool
  | .final .diverged => true
  | _ => false

private def ioEventSizes : Nat × Nat :=
  let event : HolIoEvent :=
    { name := nameOf, configuration := conf, bytes := [(w8 1, w8 2)] }
  (event.configuration.length, event.bytes.length)

private def hostOf : HolFfiResult Nat → Option Nat
  | .ret state _ => some state.ffiState
  | .final _ => none

private def eventCountOf : HolFfiResult Nat → Option Nat
  | .ret state _ => some state.ioEvents.length
  | .final _ => none

private def bytesOf : HolFfiResult Nat → Option (List W)
  | .ret _ bytes => some bytes
  | .final _ => none

private def outcomeOf : HolFfiResult Nat → Option HolFfiOutcome
  | .final event => some event.outcome
  | .ret _ _ => none

/-- Oracle shapes pinned to the HOL rows. -/
example : (HolFfiOutcome.failed == HolFfiOutcome.failed) = true := rfl
example : (HolShmemOp.mappedRead == HolShmemOp.mappedRead) = true := rfl
example : (HolFfiName.extCall (.implode [w8 102]) == nameOf) = true := rfl
example : isDiverged (.final (HolFfiOutcome.diverged) : HolOracleResult Nat) = true := rfl
example : st.ffiState = 0 := rfl
example : st.ioEvents.length = 0 := rfl
example : ioEventSizes = (2, 1) := rfl

/-- `call_FFI` cases pinned to the HOL rows. -/
example :
    hostOf (callFFIHOL st (.extCall (.implode [])) conf one) = some 0 ∧
      eventCountOf (callFFIHOL st (.extCall (.implode [])) conf one) = some 0 ∧
      bytesOf (callFFIHOL st (.extCall (.implode [])) conf one) = some one :=
  ⟨rfl, rfl, rfl⟩

example : hostOf (callFFIHOL st nameOf conf one) = some 1 := rfl
example : eventCountOf (callFFIHOL st nameOf conf one) = some 1 := rfl
example : bytesOf (callFFIHOL st nameOf conf one) = some one := rfl

example :
    outcomeOf (callFFIHOL (initialHolFfiState obad 0) nameOf conf one) =
      some HolFfiOutcome.failed := rfl

example :
    outcomeOf (callFFIHOL (initialHolFfiState ofin 0) nameOf conf one) =
      some HolFfiOutcome.diverged := rfl

private def carrierGuard : Bool :=
  (HolFfiOutcome.failed == HolFfiOutcome.failed) &&
    (HolShmemOp.mappedWrite == HolShmemOp.mappedWrite) &&
    (isDiverged (.final (HolFfiOutcome.diverged) : HolOracleResult Nat)) &&
    (st.ffiState == 0) && (st.ioEvents.length == 0) &&
    (ioEventSizes == (2, 1)) &&
    (hostOf (callFFIHOL st (.extCall (.implode [])) conf one) == some 0) &&
    (eventCountOf (callFFIHOL st (.extCall (.implode [])) conf one) == some 0) &&
    (bytesOf (callFFIHOL st (.extCall (.implode [])) conf one) == some one) &&
    (hostOf (callFFIHOL st nameOf conf one) == some 1) &&
    (eventCountOf (callFFIHOL st nameOf conf one) == some 1) &&
    (bytesOf (callFFIHOL st nameOf conf one) == some one) &&
    (outcomeOf (callFFIHOL (initialHolFfiState obad 0) nameOf conf one) ==
      some HolFfiOutcome.failed) &&
    (outcomeOf (callFFIHOL (initialHolFfiState ofin 0) nameOf conf one) ==
      some HolFfiOutcome.diverged)

#eval carrierGuard
#guard carrierGuard

/-- Runs the FFI carrier parity checks. -/
def runChecks : IO Bool := do
  if carrierGuard then
    IO.println "PASS exact HOL ffi carriers and call_FFI match the oracle rows"
    pure true
  else
    IO.println "FAIL exact HOL ffi carriers and call_FFI"
    pure false

end Flapjack.Test.FfiHOLParity
