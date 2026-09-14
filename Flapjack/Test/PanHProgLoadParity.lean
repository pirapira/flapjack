import Flapjack.PanHProgLoad

/-!
# Parity checks for Pancake `h_prog_sh_mem_load_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_sh_mem_load_probe.out` is generated from
`pan_itreeSemScript.sml:466-513`.  The Lean checks cover original-address
payloads, aligned nonzero domain checks, destination updates, invalid/domain
errors, length mismatch, and terminal oracle results.
-/

namespace Flapjack.Test.PanHProgLoadParity

open Flapjack

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

def setDestination : Nat → Nat → Nat := fun _ value => value

def zeroTree : PanFfiTree (PanHProgLoadResult Nat) :=
  panHProgShMemLoad allDomainByteContext 0 99 setDestination .opW
    (some (.word 3)) (some (.word 0))

def alignedTree : PanFfiTree (PanHProgLoadResult Nat) :=
  panHProgShMemLoad word32Context 0 99 setDestination .op8
    (some (.word 3)) (some (.word 0))

def domainErrorTree : PanFfiTree (PanHProgLoadResult Nat) :=
  panHProgShMemLoad (byteContext (fun _ => false) id) 0 99 setDestination .opW
    (some (.word 3)) (some (.word 0))

def invalidTree : PanFfiTree (PanHProgLoadResult Nat) :=
  panHProgShMemLoad allDomainByteContext 0 99 setDestination .opW
    (some (.rStruct [])) none

def returningWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [9], state := 0 }

def shortWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [], state := 0 }

def finalWorld : PanFfiWorld Nat :=
  { oracle := fun _ _ _ _ => .final .failed, state := 0 }

def observeZeroWidth : Bool :=
  match zeroTree with
  | .vis (.sharedMem .mappedRead) [0] [3] _ => true
  | _ => false

def observeAlignedOriginal : Bool :=
  match alignedTree with
  | .vis (.sharedMem .mappedRead) [1] [3, 0, 0, 0] _ => true
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
  | some (.ret (.normal state), world) => state == 9 && world.state == 0
  | _ => false

def observeMismatch : Bool :=
  match compFfi 1 zeroTree shortWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 99 && event.bytes == [3] && event.outcome == .failed
  | _ => false

def observeFinal : Bool :=
  match compFfi 1 zeroTree finalWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 99 && event.bytes == [3] && event.outcome == .failed
  | _ => false

#guard observeZeroWidth
#guard observeAlignedOriginal
#guard observeDomainError
#guard observeInvalid
#guard observeReturn
#guard observeMismatch
#guard observeFinal

def runChecks : IO Bool := do
  if observeZeroWidth then IO.println "PASS h_prog_sh_mem_load zero width" else IO.println "FAIL h_prog_sh_mem_load zero width"
  if observeAlignedOriginal then IO.println "PASS h_prog_sh_mem_load aligned original payload" else IO.println "FAIL h_prog_sh_mem_load aligned original payload"
  if observeDomainError then IO.println "PASS h_prog_sh_mem_load domain error" else IO.println "FAIL h_prog_sh_mem_load domain error"
  if observeInvalid then IO.println "PASS h_prog_sh_mem_load invalid operands" else IO.println "FAIL h_prog_sh_mem_load invalid operands"
  if observeReturn then IO.println "PASS h_prog_sh_mem_load Oracle_return" else IO.println "FAIL h_prog_sh_mem_load Oracle_return"
  if observeMismatch then IO.println "PASS h_prog_sh_mem_load length failure" else IO.println "FAIL h_prog_sh_mem_load length failure"
  if observeFinal then IO.println "PASS h_prog_sh_mem_load Oracle_final" else IO.println "FAIL h_prog_sh_mem_load Oracle_final"
  pure (observeZeroWidth && observeAlignedOriginal && observeDomainError && observeInvalid &&
    observeReturn && observeMismatch && observeFinal)

end Flapjack.Test.PanHProgLoadParity
