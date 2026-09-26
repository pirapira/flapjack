import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
Direct original-HOL evaluator rows for the exact executable `crepSem$eval_def`
port. Expected values are transcribed from `crep_eval_probe.out`,
`crep_eval_op_rv64_probe.out`, `crep_eval_crepop_mul_rv64_probe.out`,
`crep_eval_cmp_rv64_probe.out`, `crep_eval_shift_rv64_probe.out`,
`crep_eval_load_32_probe.out`, and `crep_eval_load_byte_probe.out`.
-/

namespace Flapjack.Test.CrepSemEvalExactParity

open Flapjack

def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
def word64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

def exactLocals8 : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.update HolFiniteMapExact.empty (1, .word (word8 7))

def exactGlobals8 : HolFiniteMapExact (BitVec 5) (HolWordLab 8) :=
  HolFiniteMapExact.update HolFiniteMapExact.empty (4, .word (word8 11))

def exactDomain8 (address : BitVec 8) : Prop := address = word8 3

def exactFfi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

def exactState8 : CrepSemHOLState 8 Unit where
  locals := exactLocals8
  globals := exactGlobals8
  code := HolFiniteMapExact.empty
  memory := fun address => if address == word8 3 then .word (word8 9) else .word 0
  memaddrs := exactDomain8
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := exactFfi
  baseAddr := word8 12
  topAddr := word8 13

local instance : DecidablePred exactState8.memaddrs := by
  intro address
  change Decidable (address = word8 3)
  infer_instance

def exactDomain64 (address : BitVec 64) : Prop := address = word64 8

def exactState64 : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word (word64 0x1122334455667788)
  memaddrs := exactDomain64
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := exactFfi
  baseAddr := word64 0
  topAddr := word64 0

local instance : DecidablePred exactState64.memaddrs := by
  intro address
  change Decidable (address = word64 8)
  infer_instance

#guard evalCrepSemHOLExp exactState8 (.const (word8 5)) == some (.word (word8 5))
#guard evalCrepSemHOLExp exactState8 (.var 1) == some (.word (word8 7))
#guard evalCrepSemHOLExp exactState8 (.var 2) == none
#guard evalCrepSemHOLExp exactState8 (.load (.const (word8 3))) == some (.word (word8 9))
#guard evalCrepSemHOLExp exactState8 (.load (.const (word8 8))) == none
#guard evalCrepSemHOLExp exactState8 (.loadGlob 4) == some (.word (word8 11))
#guard evalCrepSemHOLExp exactState8 (.loadGlob 8) == none
#guard evalCrepSemHOLExp exactState8 .baseAddr == some (.word (word8 12))
#guard evalCrepSemHOLExp exactState8 .topAddr == some (.word (word8 13))
#guard evalCrepSemHOLExp exactState8
    (.op .add [.const (word8 3), .const (word8 4)]) == some (.word (word8 7))
#guard evalCrepSemHOLExp exactState8
    (.op .sub [.const (word8 7), .const (word8 2)]) == some (.word (word8 5))
#guard evalCrepSemHOLExp exactState8 (.op .add []) == some (.word (word8 0))
#guard evalCrepSemHOLExp exactState8 (.op .sub [.const (word8 3)]) == none
#guard evalCrepSemHOLExp exactState8
    (.crepOp .mul [.const (word8 6), .const (word8 7)]) == some (.word (word8 42))
#guard evalCrepSemHOLExp exactState8 (.crepOp .mul [.const (word8 3)]) == none
#guard evalCrepSemHOLExp exactState8
    (.cmp .equal (.const (word8 5)) (.const (word8 5))) == some (.word (word8 1))
#guard evalCrepSemHOLExp exactState8
    (.cmp .equal (.const (word8 5)) (.const (word8 6))) == some (.word (word8 0))
#guard evalCrepSemHOLExp exactState8
    (.shift .lsl (.const (word8 1)) (.const (word8 3))) == some (.word (word8 8))
#guard evalCrepSemHOLExp exactState8
    (.shift .lsl (.const (word8 1)) (.const (word8 8))) == none
#guard evalCrepSemHOLExp exactState64 (.load32 (.const (word64 8))) ==
    some (.word (word64 0x55667788))
#guard evalCrepSemHOLExp exactState64 (.loadByte (.const (word64 8))) ==
    some (.word (word64 136))

end Flapjack.Test.CrepSemEvalExactParity
