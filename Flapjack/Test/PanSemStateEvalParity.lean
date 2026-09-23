import Flapjack.Pancake.Semantics.PanSemStateEval

/-! The expected values are recorded by direct HOL EVAL of the source
`panSem$eval` probe. The Lean cases exercise the state-derived word and memory
inputs against those checked-in results. -/

namespace Flapjack.Test.PanSemStateEvalParity

open Flapjack

private abbrev Word64 := RiscV.Word 64

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:209-297 (eval_def)"

def originalProbeCommand : String :=
  "HOL_PROBE_ONLY=pan_sem_state_eval_probeScript.sml scripts/hol-probes/regenerate.sh"

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:209-297 (eval_def)"
#guard originalProbeCommand ==
  "HOL_PROBE_ONLY=pan_sem_state_eval_probeScript.sml scripts/hol-probes/regenerate.sh"

def sourceMemoryWord : Word64 := BitVec.ofNat 64 0x1122334455667788

def sourceState (bigEndian inWordDomain inSharedDomain : Bool) :
    PanSemState Word64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    exceptionShapes := fun _ => none
    memory := fun address =>
      if address == 0 then some (.word sourceMemoryWord) else none
    memaddrs := fun _ => inWordDomain
    sharedMemaddrs := fun _ => inSharedDomain
    clock := 0
    be := bigEndian
    ffi := ()
    baseAddress := 0
    topAddress := 0 }

private def isWordResult (result : Option (PanValue Word64))
    (expected : Word64) : Bool :=
  match result with
  | some (.word value) => value == expected
  | _ => false

private def isNoneResult {α : Type} (result : Option α) : Bool :=
  match result with
  | none => true
  | some _ => false

def littleEndianState : PanSemState Word64 Unit := sourceState false true true
def bigEndianState : PanSemState Word64 Unit := sourceState true true true

#guard isWordResult
  (evalPanSemStateExp littleEndianState (.load .one (.const 0)))
  sourceMemoryWord
#guard isNoneResult (evalPanSemStateExp (sourceState false false true)
  (.load .one (.const 0)))
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.loadByte (.const 0)))
  (BitVec.ofNat 64 0x88)
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.loadByte (.const 7)))
  (BitVec.ofNat 64 0x11)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.loadByte (.const 0)))
  (BitVec.ofNat 64 0x11)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.loadByte (.const 7)))
  (BitVec.ofNat 64 0x88)
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.load32 (.const 0)))
  (BitVec.ofNat 64 0x55667788)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.load32 (.const 0)))
  (BitVec.ofNat 64 0x11223344)

#guard isWordResult ((panSemBitVec64MemoryAccess littleEndianState).sharedRead
  littleEndianState.memory panSemBitVec64BytesInWord .opW 0)
  sourceMemoryWord
#guard isNoneResult ((panSemBitVec64MemoryAccess
  (sourceState false true false)).sharedRead
    littleEndianState.memory panSemBitVec64BytesInWord .opW 0)

end Flapjack.Test.PanSemStateEvalParity
