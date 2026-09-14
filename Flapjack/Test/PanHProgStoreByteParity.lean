import Flapjack.PanHProgStoreByte

/-!
# Parity checks for Pancake `h_prog_store_byte_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_store_byte_probe.out` is generated from
`pan_itreeSemScript.sml:287-296`.  Lean checks cover successful memory update,
out-of-domain failure, and invalid operands.
-/

namespace Flapjack.Test.PanHProgStoreByteParity

open Flapjack

def storeByte : Nat → Nat → Nat → Option Nat
  | state, address, value => if address == 3 then some (state + value) else none

def observeSuccess : Bool :=
  match panHProgStoreByte 0 storeByte id (some 3) (some 7) with
  | .ret (.normal state) => state == 7
  | _ => false

def observeDomainError : Bool :=
  match panHProgStoreByte 0 storeByte id (some 4) (some 7) with
  | .ret (.error state) => state == 0
  | _ => false

def observeInvalid : Bool :=
  match panHProgStoreByte 0 storeByte id none (some 7) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeSuccess
#guard observeDomainError
#guard observeInvalid

def runChecks : IO Bool := do
  if observeSuccess then IO.println "PASS h_prog_store_byte success" else IO.println "FAIL h_prog_store_byte success"
  if observeDomainError then IO.println "PASS h_prog_store_byte domain error" else IO.println "FAIL h_prog_store_byte domain error"
  if observeInvalid then IO.println "PASS h_prog_store_byte invalid operands" else IO.println "FAIL h_prog_store_byte invalid operands"
  pure (observeSuccess && observeDomainError && observeInvalid)

end Flapjack.Test.PanHProgStoreByteParity
