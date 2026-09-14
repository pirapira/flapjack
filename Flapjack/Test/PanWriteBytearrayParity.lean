import Flapjack.PanWriteBytearray
import Flapjack.CrepeRuntime

/-!
# Parity checks for Pancake `write_bytearray_def`

The direct HOL fixture in `scripts/hol-probes/pan_write_bytearray_probe.out`
covers the active tail-first definition.  These checks exercise two
successful byte writes, preservation of an unrelated cell, and the source
behavior when the tail store cannot be performed.
-/

namespace Flapjack.Test.PanWriteBytearrayParity

open Flapjack

def model : PanMemoryModel Nat := natCrepRuntimeMemoryModel

def memory : Nat → Option (PanValue Nat)
  | 3 => some (.word 0)
  | 4 => some (.word 0)
  | _ => none

def domain : Nat → Bool := fun _ => true

def written : Nat → Option (PanValue Nat) :=
  panSemWriteBytearray model 3 [7, 8] memory domain 1 false

def observeWrites : Bool :=
  match written 3, written 4 with
  | some (.word first), some (.word second) => first == 7 && second == 8
  | _, _ => false

def observeSibling : Bool := (written 5).isNone

def missingTailMemory : Nat → Option (PanValue Nat)
  | 3 => some (.word 0)
  | _ => none

def missingTailWritten : Nat → Option (PanValue Nat) :=
  panSemWriteBytearray model 3 [7, 8] missingTailMemory domain 1 false

def observeFailedTailKeepsCurrentInput : Bool :=
  match missingTailWritten 3 with
  | some (.word value) => value == 7
  | _ => false

def observeFailedTailKeepsMissingCell : Bool := (missingTailWritten 4).isNone

#guard observeWrites
#guard observeSibling
#guard observeFailedTailKeepsCurrentInput
#guard observeFailedTailKeepsMissingCell

def runChecks : IO Bool := do
  if observeWrites then IO.println "PASS Pan write_bytearray writes tail and current"
  else IO.println "FAIL Pan write_bytearray writes tail and current"
  if observeSibling then IO.println "PASS Pan write_bytearray preserves sibling"
  else IO.println "FAIL Pan write_bytearray preserves sibling"
  if observeFailedTailKeepsCurrentInput then
    IO.println "PASS Pan write_bytearray failed tail keeps current input"
  else IO.println "FAIL Pan write_bytearray failed tail keeps current input"
  if observeFailedTailKeepsMissingCell then
    IO.println "PASS Pan write_bytearray failed tail keeps missing cell"
  else IO.println "FAIL Pan write_bytearray failed tail keeps missing cell"
  pure (observeWrites && observeSibling && observeFailedTailKeepsCurrentInput &&
    observeFailedTailKeepsMissingCell)

end Flapjack.Test.PanWriteBytearrayParity
