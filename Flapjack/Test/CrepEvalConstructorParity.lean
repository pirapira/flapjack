import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.RiscV.PanMemory

/-!
Direct width-8 word-result constructor checks matching
`scripts/hol-probes/crep_eval_probe.out`. The evaluator equations are generic
in their word carrier and do not pass through `riscvCrepWordTarget`; the state
below only supplies the production evaluator's existing runtime fields.
-/

namespace Flapjack.Test.CrepEvalConstructorParity

open Flapjack

def word8 (n : Nat) : RiscV.Word 8 := BitVec.ofNat 8 n

def word8FfiContext : PanValueFfiContext (RiscV.Word 8) where
  sharedDomain := fun _ => false
  byteAlign := fun address => address
  bigEndian := false
  wordToBytes := fun value _ => [UInt8.ofNat value.toNat]
  wordOfBytes := fun _ bytes => BitVec.ofNat 8 ((bytes.headD 0).toNat)
  wordToByte := fun value => UInt8.ofNat value.toNat
  byteToWord := fun byte => BitVec.ofNat 8 byte.toNat
  valueToNat := fun value => value.toNat

def probeState : CrepRuntimeState (RiscV.Word 8) Unit :=
  { locals := fun name => if name == 1 then some (.word (word8 7)) else none
    globals := fun address =>
      if address == (4 : BitVec 5) then some (.word (word8 11)) else none
    code := FEMPTY
    memory := fun address => if address == word8 3 then .word (word8 9) else .word 0
    memaddrs := fun address => address == word8 3
    shMemaddrs := fun _ => false
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := word8 1
    ffiContext := word8FfiContext
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := word8 12
    topAddress := word8 13 }

/- HOL crep_eval_probe: const, local hit/miss, word load hit/miss, and global
   hit return the corresponding Word word_lab values or NONE. -/
#guard (evalCrepRuntimeExp probeState (.const (word8 5))).map PanWordLab.word ==
  some (.word (word8 5))
#guard (evalCrepRuntimeExp probeState (.var 1)).map PanWordLab.word ==
  some (.word (word8 7))
#guard (evalCrepRuntimeExp probeState (.var 2)).map PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState (.load (.const (word8 3)))).map PanWordLab.word ==
  some (.word (word8 9))
#guard (evalCrepRuntimeExp probeState (.load (.const (word8 8)))).map PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState (.loadGlob (4 : BitVec 5))).map PanWordLab.word ==
  some (.word (word8 11))
#guard (evalCrepRuntimeExp probeState (.loadGlob (8 : BitVec 5))).map PanWordLab.word == none
/- HOL crep_arith_eval_mul_const_probe: the general multiplier case leaves
   Crepop Mul [Var 1; Const 3w], which evaluates to Word 21w. -/
#guard (evalCrepRuntimeExp probeState
    (.crepOp .mul [.var 1, .const (word8 3)])).map PanWordLab.word ==
  some (.word (word8 21))
#guard (evalCrepRuntimeExp probeState (.crepOp .mul [.const (word8 4)])).map
    PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState .baseAddr).map PanWordLab.word ==
  some (.word (word8 12))
#guard (evalCrepRuntimeExp probeState .topAddr).map PanWordLab.word ==
  some (.word (word8 13))

example : (evalCrepRuntimeExp probeState (.var 1)).map PanWordLab.word =
    some (.word (word8 7)) :=
  evalCrepRuntimeExp_var_wordLab probeState 1

example : (evalCrepRuntimeExp probeState (.load (.const (word8 3)))).map
    PanWordLab.word = some (.word (word8 9)) := by
  rw [evalCrepRuntimeExp_load_wordLab]
  simp [evalCrepRuntimeExp, probeState, word8]

end Flapjack.Test.CrepEvalConstructorParity
