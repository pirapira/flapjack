import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeSimpExpParity

/-! HOL words use a finite Boolean-function carrier. This direct check
    exercises its `Fin n` encoding and conversion to the production BitVec
    representation independently of the expression evaluator bridge. -/
def holBits4 : Fin 4 → Bool := fun index => index.val == 0 || index.val == 2

#guard holWordBitsToBitVec holBits4 == BitVec.ofNat 4 5
#guard holWordBitsToBitVec (holBits4 + holBits4) == BitVec.ofNat 4 10
#guard holWordBitsToBitVec (holBits4 * holBits4) == BitVec.ofNat 4 9

example : bitVecToHolWordBits (holWordBitsToBitVec holBits4) = holBits4 :=
  bitVecToHolWordBits_holWordBitsToBitVec holBits4

example :
    holWordBitsToBitVec (bitVecToHolWordBits (BitVec.ofNat 4 5)) =
      BitVec.ofNat 4 5 :=
  holWordBitsToBitVec_bitVecToHolWordBits (BitVec.ofNat 4 5)

#guard crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat 4 value))
    (.crepOp .mul [.var 2, .const (bitVecToHolWordBits (BitVec.ofNat 4 2))]) ==
  .shift .lsl (.var 2) (.const (bitVecToHolWordBits (BitVec.ofNat 4 1)))

def holWordBitsState4 : CrepHolState (Fin 4 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word holBits4
  memaddrs := fun _ => false
  shMemaddrs := fun _ => false
  clock := 0
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holBits4
  topAddress := holBits4

#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime (.const holBits4) ==
  some holBits4
#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
    (.crepOp .mul [.const holBits4, .const holBits4]) ==
  some (bitVecToHolWordBits (BitVec.ofNat 4 9))

/-! Direct parity for `crep_arith$simp_exp_def`
    (`crep_arithScript.sml:59`).  These cases cover constant folding,
    constant-on-either-side multiplication, recursive children, and the
    unchanged fallback shape. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.const (word8 2), .const (word8 3)]) with
  | .const value => value == word8 6
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.const (word8 2), .var 2]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.var 2, .const (word8 2)]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.var 2, .const (word8 3)]) with
  | .crepOp .mul [.var 2, .const value] => value == word8 3
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.load (.crepOp .mul [.var 2, .const (word8 2)])) with
  | .load (.shift .lsl (.var 2) (.const value)) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul
        [.crepOp .mul [.const (word8 2), .const (word8 3)],
         .const (word8 4)]) with
  | .const value => value == word8 24
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8) (.var 7 : CrepExp (RiscV.Word 8)) with
  | .var 7 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

def noWords : RiscV.Word 64 → PanWordLab (RiscV.Word 64) := fun _ => .word 0
def noDomain : RiscV.Word 64 → Bool := fun _ => false

def runtimeBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noWords
    memaddrs := noDomain
    shMemaddrs := noDomain
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := (8 : RiscV.Word 64)
    ffiContext := riscv64PanValueFfiContext noDomain
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def runtimeState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { riscv64CrepRuntimeTarget runtimeBase with
    locals := updateCrepRuntimeLocal (fun _ => none) 2 (.word (7 : RiscV.Word 64)) }

/-! These checks exercise the production evaluator before and after the pass,
    including the power-of-two shift branch and bottom-up nested folding.
    They are executable support checks while the polymorphic HOL theorem port
    remains open. -/
def runtimeEvalSimpParity : Bool :=
  let source : CrepExp (RiscV.Word 64) :=
    .crepOp .mul [.var 2, .const (8 : RiscV.Word 64)]
  let nested : CrepExp (RiscV.Word 64) :=
    .crepOp .mul [source, .const (3 : RiscV.Word 64)]
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState) source == some 56 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepSimpExp (BitVec.ofNat 64) source) == some 56 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState) nested == some 168 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepSimpExp (BitVec.ofNat 64) nested) == some 168

#guard runtimeEvalSimpParity

/-! An 8-bit all-width instance exercises the source-shaped state adapter and
    the proved production evaluator correspondence, beyond the RV64 executable
    fixture above. This remains untagged support for the arbitrary HOL word
    carrier gap documented beside `crepSimpExpCorrect1BitVec`. -/
def holState8 : CrepHolState (RiscV.Word 8) Unit :=
  { locals := updateCrepRuntimeLocal (fun _ => none) 2 (.word (word8 7))
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def holExpression8 : CrepExp (RiscV.Word 8) :=
  .crepOp .mul [.var 2, .const (word8 8)]

example :
    evalCrepHolExpWordLab (crepArithHolMapCode (fun entry => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
    evalCrepHolExpWordLab holState8 holExpression8 := by
  apply crepSimpExpCorrect1BitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal]

example :
    evalCrepHolExpWordLab (crepArithHolMapCode (fun entry => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
      some (.word (word8 56)) := by
  apply crepSimpExpCorrectBitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal, panTheWord, word8]

end Flapjack.Test.CrepeSimpExpParity
