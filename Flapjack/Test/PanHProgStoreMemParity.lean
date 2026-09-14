import Flapjack.PanHProgStoreMem

/-!
# Parity checks for Pancake `h_prog_store_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_store_probe.out` comes from
`pan_itreeSemScript.sml:277-285`.  These checks cover flattened word stores,
domain failure, and malformed operands.
-/

namespace Flapjack.Test.PanHProgStoreMemParity

open Flapjack

def store : Nat → Nat → List Nat → Option Nat :=
  fun state address values =>
    if address == 3 then some (state + values.foldl (· + ·) 0) else none

def observeSuccess : Bool :=
  match panHProgStoreMem 0 store panValueFlatWords (some 3) (some (.word 7)) with
  | .ret (.normal state) => state == 7
  | _ => false

def observeStructured : Bool :=
  match panHProgStoreMem 0 store panValueFlatWords (some 3)
      (some (.rStruct [.word 2, .word 5])) with
  | .ret (.normal state) => state == 7
  | _ => false

def observeDomainError : Bool :=
  match panHProgStoreMem 0 store panValueFlatWords (some 4) (some (.word 7)) with
  | .ret (.error state) => state == 0
  | _ => false

def observeInvalid : Bool :=
  match panHProgStoreMem 0 store panValueFlatWords none (some (.word 7)) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeSuccess
#guard observeStructured
#guard observeDomainError
#guard observeInvalid

def runChecks : IO Bool := do
  if observeSuccess then IO.println "PASS h_prog_store word payload" else IO.println "FAIL h_prog_store word payload"
  if observeStructured then IO.println "PASS h_prog_store flattened payload" else IO.println "FAIL h_prog_store flattened payload"
  if observeDomainError then IO.println "PASS h_prog_store domain error" else IO.println "FAIL h_prog_store domain error"
  if observeInvalid then IO.println "PASS h_prog_store invalid operands" else IO.println "FAIL h_prog_store invalid operands"
  pure (observeSuccess && observeStructured && observeDomainError && observeInvalid)

end Flapjack.Test.PanHProgStoreMemParity
