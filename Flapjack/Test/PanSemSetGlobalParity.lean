import Flapjack.PanSemSetGlobal

/-!
# Parity checks for `panSem$set_global_def`

The direct HOL fixture in `scripts/hol-probes/pan_sem_set_global_probe.out`
evaluates the original state update.  Lean checks cover insertion, overwrite,
sibling preservation, and local-map preservation.
-/

namespace Flapjack.Test.PanSemSetGlobalParity

open Flapjack

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def locals : String → Option (PanValue Nat)
  | "x" => some (.word 9)
  | _ => none

def globals : String → Option (PanValue Nat)
  | "g" => some (.word 1)
  | _ => none

def state : PanKvarState Nat := { locals := locals, globals := globals }

def observeInsert : Bool :=
  isWord 5 (panSemSetGlobal { locals := locals, globals := fun _ => none }
    "g" (.word 5) |>.globals "g")

def observeOverwrite : Bool :=
  isWord 5 (panSemSetGlobal state "g" (.word 5) |>.globals "g")

def observeSibling : Bool :=
  isWord 1 (panSemSetGlobal state "h" (.word 7) |>.globals "g")

def observeLocals : Bool :=
  isWord 9 (panSemSetGlobal state "g" (.word 5) |>.locals "x")

#guard observeInsert
#guard observeOverwrite
#guard observeSibling
#guard observeLocals

def runChecks : IO Bool := do
  if observeInsert then IO.println "PASS Pan sem set_global insert"
  else IO.println "FAIL Pan sem set_global insert"
  if observeOverwrite then IO.println "PASS Pan sem set_global overwrite"
  else IO.println "FAIL Pan sem set_global overwrite"
  if observeSibling then IO.println "PASS Pan sem set_global sibling"
  else IO.println "FAIL Pan sem set_global sibling"
  if observeLocals then IO.println "PASS Pan sem set_global locals"
  else IO.println "FAIL Pan sem set_global locals"
  pure (observeInsert && observeOverwrite && observeSibling && observeLocals)

end Flapjack.Test.PanSemSetGlobalParity
