import Flapjack.PanSemWriteBytearray

/-!
# Parity checks for `panSem$write_bytearray_def`

The direct HOL fixture covers the empty, in-domain, and failed-domain cases.
Lean checks exercise recursive tail-first writes and the source fallback on a
missing memory domain.
-/

namespace Flapjack.Test.PanSemWriteBytearrayParity

open Flapjack

def context : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def access (domain : Nat → Bool) : PanValueMemoryAccess Nat :=
  { domain := domain
    wordOp := fun _ _ => some 0
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => some 0
    readWord := fun _ _ _ _ => none
    readByte := fun _ _ _ _ => none
    read16 := fun _ _ _ _ => none
    read32 := fun _ _ _ _ => none
    storeWord := fun _ _ _ _ _ => none
    storeByte := fun domain memory _ address value =>
      if domain address then some (updatePanValueMemory memory address (.word value))
      else none
    store16 := fun _ _ _ _ _ => none
    store32 := fun _ _ _ _ _ => none
    sharedRead := fun _ _ _ _ => none
    sharedStore := fun _ _ _ _ _ => none }

def initial : Nat → Option (PanValue Nat) :=
  fun address => if address == 0 then some (.word 1) else none

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def isNone : Option (PanValue Nat) → Bool
  | none => true
  | some _ => false

def written := panSemWriteBytearray (access (fun _ => true)) context initial 1 0 [7, 8]
def failed := panSemWriteBytearray (access (fun address => address == 1)) context initial 1 0 [7, 8]

def tailFirst : Bool :=
  match written 0, written 1 with
  | some (.word first), some (.word second) => first == 7 && second == 8
  | _, _ => false

def fallback : Bool :=
  match failed 0, failed 1 with
  | some (.word first), second => first == 1 && isNone second
  | _, _ => false

def empty : Bool :=
  isWord 1 (panSemWriteBytearray (access (fun _ => true)) context initial 1 0 [] 0)

#guard tailFirst
#guard fallback
#guard empty

def runChecks : IO Bool := do
  if tailFirst then IO.println "PASS Pan sem write_bytearray tail-first recursion"
  else IO.println "FAIL Pan sem write_bytearray tail-first recursion"
  if fallback then IO.println "PASS Pan sem write_bytearray domain fallback"
  else IO.println "FAIL Pan sem write_bytearray domain fallback"
  if empty then IO.println "PASS Pan sem write_bytearray empty"
  else IO.println "FAIL Pan sem write_bytearray empty"
  pure (tailFirst && fallback && empty)

end Flapjack.Test.PanSemWriteBytearrayParity
