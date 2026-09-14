import Flapjack.PanHProgStore32

/-!
# Parity checks for Pancake `h_prog_store_32_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_store_32_probe.out` is generated from
`pan_itreeSemScript.sml:297-306`.  Lean checks cover the successful memory
update, alignment/domain failure, and invalid operands.
-/

namespace Flapjack.Test.PanHProgStore32Parity

open Flapjack

def store32 : Nat → Nat → Nat → Option Nat
  | state, address, value => if address == 4 then some (state + value) else none

def observeSuccess : Bool :=
  match panHProgStore32 0 store32 (some 4) (some 7) with
  | .ret (.normal state) => state == 7
  | _ => false

def observeDomainError : Bool :=
  match panHProgStore32 0 store32 (some 8) (some 7) with
  | .ret (.error state) => state == 0
  | _ => false

def observeInvalid : Bool :=
  match panHProgStore32 0 store32 none (some 7) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeSuccess
#guard observeDomainError
#guard observeInvalid

def runChecks : IO Bool := do
  if observeSuccess then IO.println "PASS h_prog_store_32 success" else IO.println "FAIL h_prog_store_32 success"
  if observeDomainError then IO.println "PASS h_prog_store_32 domain error" else IO.println "FAIL h_prog_store_32 domain error"
  if observeInvalid then IO.println "PASS h_prog_store_32 invalid operands" else IO.println "FAIL h_prog_store_32 invalid operands"
  pure (observeSuccess && observeDomainError && observeInvalid)

end Flapjack.Test.PanHProgStore32Parity
