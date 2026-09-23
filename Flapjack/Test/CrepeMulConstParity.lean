import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeMulConstParity

/-! Direct parity for `crep_arith$mul_const_def`
    (`crep_arithScript.sml:50`).  The cases cover the zero, one, power-of-two,
    and general-constant branches of the original definition. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def expression : CrepExp (RiscV.Word 8) := .var 2
def runtimeExpression : CrepExp (RiscV.Word 64) := .var 2

def parityGuard : Bool :=
  (match crepMulConst (BitVec.ofNat 8) expression (word8 0) with
  | .const value => value == word8 0
  | _ => false) &&
  (match crepMulConst (BitVec.ofNat 8) expression (word8 1) with
  | .var 2 => true
  | _ => false) &&
  (match crepMulConst (BitVec.ofNat 8) expression (word8 2) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepMulConst (BitVec.ofNat 8) expression (word8 3) with
  | .crepOp .mul [.var 2, .const value] => value == word8 3
  | _ => false) &&
  (match crepMulConst (BitVec.ofNat 8) expression (word8 4) with
  | .shift .lsl (.var 2) (.const value) => value == word8 2
  | _ => false) &&
  (match crepMulConst (BitVec.ofNat 8) expression (word8 8) with
  | .shift .lsl (.var 2) (.const value) => value == word8 3
  | _ => false)

def noRiscVWords : RiscV.Word 64 → Option (RiscV.Word 64) := fun _ => none
def noRiscVDomain : RiscV.Word 64 → Bool := fun _ => false

def runtimeBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noRiscVWords
    memaddrs := noRiscVDomain
    shMemaddrs := noRiscVDomain
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := (8 : RiscV.Word 64)
    ffiContext := riscv64PanValueFfiContext noRiscVDomain
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def runtimeState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { riscv64CrepRuntimeTarget runtimeBaseState with
    locals := updateCrepRuntimeLocal (fun _ => none) 2 (.word (7 : RiscV.Word 64)) }

def evaluateMulConst (multiplier : RiscV.Word 64) : Option (RiscV.Word 64) :=
  evalCrepRuntimeExp runtimeState
    (crepMulConst (BitVec.ofNat 64) (.var 2) multiplier)

/-! Direct `crep_arith_eval_mul_const_probe.out` parity: the input is
    `SOME (Word 7w)`; zero, one, power-of-two 8, and general 3 produce words
    0, 7, 56, and 21 respectively. -/
def runtimeParityGuard : Bool :=
  evalCrepRuntimeExp runtimeState (.var 2) == some (7 : RiscV.Word 64) &&
  evaluateMulConst 0 == some (0 : RiscV.Word 64) &&
  evaluateMulConst 1 == some (7 : RiscV.Word 64) &&
  evaluateMulConst 8 == some (56 : RiscV.Word 64) &&
  evaluateMulConst 3 == some (21 : RiscV.Word 64)

#eval parityGuard
#guard parityGuard
#guard runtimeParityGuard

private theorem runtimeInputWrapped :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState) runtimeExpression).map
      PanWordLab.word = some (.word (7 : RiscV.Word 64)) := by
  have hRaw : evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
      runtimeExpression = some (7 : RiscV.Word 64) := by native_decide
  simp [hRaw]

example : (evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepMulConst (BitVec.ofNat 64) runtimeExpression (0 : RiscV.Word 64))).map
      PanWordLab.word = some (.word 0) :=
  crepEvalMulConst runtimeState runtimeExpression 0 7 runtimeInputWrapped

example : (evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepMulConst (BitVec.ofNat 64) runtimeExpression (1 : RiscV.Word 64))).map
      PanWordLab.word = some (.word 7) :=
  crepEvalMulConst runtimeState runtimeExpression 1 7 runtimeInputWrapped

example : (evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepMulConst (BitVec.ofNat 64) runtimeExpression (8 : RiscV.Word 64))).map
      PanWordLab.word = some (.word 56) :=
  crepEvalMulConst runtimeState runtimeExpression 8 7 runtimeInputWrapped

example : (evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepMulConst (BitVec.ofNat 64) runtimeExpression (3 : RiscV.Word 64))).map
      PanWordLab.word = some (.word 21) :=
  crepEvalMulConst runtimeState runtimeExpression 3 7 runtimeInputWrapped

end Flapjack.Test.CrepeMulConstParity
