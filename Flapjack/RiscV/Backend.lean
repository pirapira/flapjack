import Flapjack.Word
import Flapjack.RiscV.Model

/-!
The first executable Word-to-RISC-V instruction-selection slice.

This is intentionally a partial compiler.  It covers the straight-line Word
fragment made of `skip`, assignments, sequencing, constants, register reads,
and addition.  The option-valued interface makes the current boundary
explicit while the remaining Word instructions are ported.
-/

namespace Flapjack.RiscV

def registerOfNat (name : Nat) : Option (Fin 32) :=
  if h : name < 32 then some ⟨name, h⟩ else none

@[simp] theorem registerOfNat_zero : registerOfNat 0 = some 0 := by
  simp [registerOfNat]

theorem registerOfNat_some_lt {name : Nat} {register : Fin 32}
    (h : registerOfNat name = some register) : name < 32 := by
  simp only [registerOfNat] at h
  split at h <;> simp_all

def wordExpToInstruction [NeZero width] (destination : Nat) :
    WordExp (Word width) → Option (Instruction width)
  | .const value => do
      let destination ← registerOfNat destination
      pure (.addi destination 0 value)
  | .var source => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.addi destination source 0)
  | .op .add [.var left, .var right] => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (.add destination left right)
  | _ => none

def wordProgToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width))
  | .skip => some []
  | .assign name value =>
      (wordExpToInstruction name value).map (fun instruction => [instruction])
  | .seq first second => do
      let first ← wordProgToRiscV first
      let second ← wordProgToRiscV second
      pure (first ++ second)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def executeInstructions [NeZero width] (state : State width) :
    List (Instruction width) → State width
  | [] => state
  | instruction :: instructions =>
      executeInstructions (execute state instruction) instructions

def evalWordExp [NeZero width] (state : State width) :
    WordExp (Word width) → Option (Word width)
  | .const value => some value
  | .var name => do
      let register ← registerOfNat name
      pure (readRegister state register)
  | .op .add [.var left, .var right] => do
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (readRegister state left + readRegister state right)
  | _ => none

def evalWordProg [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width)
  | .skip => some state
  | .assign name value => do
      let destination ← registerOfNat name
      let value ← evalWordExp state value
      pure (writeRegister { state with pc := nextPc state } destination value)
  | .seq first second => do
      let state ← evalWordProg state first
      evalWordProg state second
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem compileWordAdd_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.op .add [.var 2, .var 3])) =
      some (executeInstructions state [.add 1 2 3]) := by
  simp [evalWordProg, evalWordExp, executeInstructions, registerOfNat,
    execute, writeRegister, nextPc]

def compileWordAdd [NeZero width] (destination left right : Nat) :
    Option (List (Instruction width)) :=
  wordProgToRiscV (.assign destination (.op .add [.var left, .var right]))

example [NeZero width] :
    compileWordAdd (width := width) 1 2 3 = some [.add 1 2 3] := by
  simp [compileWordAdd, wordProgToRiscV, wordExpToInstruction, registerOfNat]

end Flapjack.RiscV
