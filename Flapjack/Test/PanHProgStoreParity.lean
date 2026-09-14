import Flapjack.PanHProgStore

/-!
# Parity checks for Pancake `h_prog_sh_mem_store_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_sh_mem_store_probe.out` is generated from
`pan_itreeSemScript.sml:513-558`. The Lean checks cover source operand/domain
errors, zero-width payload construction, nonzero alignment with the original
address retained in the payload, equal-length return, mismatch, and terminal
oracle results. Every result branch also checks the unchanged source-state
token; the direct HOL fixture projects that state for successful return,
length mismatch, and `Oracle_final` continuations.
-/

namespace Flapjack.Test.PanHProgStoreParity

open Flapjack

def sourceProbeCommand : String := "scripts/hol-probes/regenerate.sh"

#guard sourceProbeCommand == "scripts/hol-probes/regenerate.sh"

def byteContext (domain : Nat → Bool) (align : Nat → Nat) :
    PanValueFfiContext Nat :=
  { sharedDomain := domain
    byteAlign := align
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def word32Context : PanValueFfiContext Nat :=
  { byteContext (fun address => address == 0) (fun _ => 0) with
    wordToBytes := fun value _ =>
      [UInt8.ofNat value, 0, 0, 0] }

def allDomainByteContext : PanValueFfiContext Nat :=
  byteContext (fun _ => true) id

def zeroTree : PanFfiTree (PanHProgStoreResult Nat) :=
  panHProgShMemStore (σ := Nat) allDomainByteContext 0 .opW
    (some (.word 3)) (some (.word 7))

def alignedTree : PanFfiTree (PanHProgStoreResult Nat) :=
  panHProgShMemStore (σ := Nat) word32Context 0 .op8
    (some (.word 3)) (some (.word 171))

def domainErrorTree : PanFfiTree (PanHProgStoreResult Nat) :=
  panHProgShMemStore (σ := Nat) (byteContext (fun _ => false) id) 0 .opW
    (some (.word 3)) (some (.word 7))

def invalidTree : PanFfiTree (PanHProgStoreResult Nat) :=
  panHProgShMemStore (σ := Nat) allDomainByteContext 0 .opW
    (some (.rStruct [])) (some (.word 7))

def returningWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ bytes => .returned state bytes, state := 0 }

def shortWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [], state := 0 }

def finalWorld : PanFfiWorld Nat :=
  { oracle := fun _ _ _ _ => .final .failed, state := 0 }

def observeZeroWidth : Bool :=
  match zeroTree with
  | .vis (.sharedMem .mappedWrite) [0] [7, 3] _ => true
  | _ => false

def observeAlignedOriginal : Bool :=
  match alignedTree with
  | .vis (.sharedMem .mappedWrite) [1] [171, 3, 0, 0, 0] _ => true
  | _ => false

def observeDomainError : Bool :=
  match domainErrorTree with
  | .ret (.error state) => state == 0
  | _ => false

def observeInvalid : Bool :=
  match invalidTree with
  | .ret (.error state) => state == 0
  | _ => false

def observeReturn : Bool :=
  match compFfi 1 zeroTree returningWorld with
  | some (.ret (.normal state), world) => state == 0 && world.state == 0
  | _ => false

def observeMismatch : Bool :=
  match compFfi 1 zeroTree shortWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 0 && event.bytes == [7, 3] && event.outcome == .failed
  | _ => false

def observeFinal : Bool :=
  match compFfi 1 zeroTree finalWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 0 && event.bytes == [7, 3] && event.outcome == .failed
  | _ => false

#guard observeZeroWidth
#guard observeAlignedOriginal
#guard observeDomainError
#guard observeInvalid
#guard observeReturn
#guard observeMismatch
#guard observeFinal

def runChecks : IO Bool := do
  if observeZeroWidth then IO.println "PASS h_prog_sh_mem_store zero width" else IO.println "FAIL h_prog_sh_mem_store zero width"
  if observeAlignedOriginal then IO.println "PASS h_prog_sh_mem_store aligned original payload" else IO.println "FAIL h_prog_sh_mem_store aligned original payload"
  if observeDomainError then IO.println "PASS h_prog_sh_mem_store domain error" else IO.println "FAIL h_prog_sh_mem_store domain error"
  if observeInvalid then IO.println "PASS h_prog_sh_mem_store invalid operands" else IO.println "FAIL h_prog_sh_mem_store invalid operands"
  if observeReturn then IO.println "PASS h_prog_sh_mem_store Oracle_return" else IO.println "FAIL h_prog_sh_mem_store Oracle_return"
  if observeMismatch then IO.println "PASS h_prog_sh_mem_store length failure" else IO.println "FAIL h_prog_sh_mem_store length failure"
  if observeFinal then IO.println "PASS h_prog_sh_mem_store Oracle_final" else IO.println "FAIL h_prog_sh_mem_store Oracle_final"
  pure (observeZeroWidth && observeAlignedOriginal && observeDomainError && observeInvalid &&
    observeReturn && observeMismatch && observeFinal)

end Flapjack.Test.PanHProgStoreParity
