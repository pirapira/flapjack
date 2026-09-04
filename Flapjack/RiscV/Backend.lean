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
  | .op operator [.var left, .var right] => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (match operator with
        | .add => .add destination left right
        | .sub => .sub destination left right
        | .and => .and destination left right
        | .or => .or destination left right
        | .xor => .xor destination left right)
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
  | .op operator [.var left, .var right] => do
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (match operator with
        | .add => readRegister state left + readRegister state right
        | .sub => readRegister state left - readRegister state right
        | .and => readRegister state left &&& readRegister state right
        | .or => readRegister state left ||| readRegister state right
        | .xor => readRegister state left ^^^ readRegister state right)
  | _ => none

def wordFunctionToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .skip => some ([], [])
  | .assign name value => do
      let instruction ← wordExpToInstruction name value
      pure ([instruction], [])
  | .seq first second => do
      let (firstCode, firstReturns) ← wordFunctionToRiscV first
      let (secondCode, secondReturns) ← wordFunctionToRiscV second
      pure (firstCode ++ secondCode,
        if secondReturns.isEmpty then firstReturns else secondReturns)
  | .return _ values => do
      let values ← values.mapM registerOfNat
      pure ([], values)
  | _ => none

def evalWordFunction [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width × List (Word width))
  | .skip => some (state, [])
  | .assign name value => do
      let destination ← registerOfNat name
      let value ← evalWordExp state value
      pure (writeRegister { state with pc := nextPc state } destination value, [])
  | .seq first second => do
      let (state, firstReturns) ← evalWordFunction state first
      let (state, secondReturns) ← evalWordFunction state second
      pure (state, if secondReturns.isEmpty then firstReturns else secondReturns)
  | .return _ values => do
      let values ← values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister state register))
      pure (state, values)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

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

theorem wordExpToInstruction_binOp [NeZero width] (operator : BinOp) :
    wordExpToInstruction (width := width) 1 (.op operator [.var 2, .var 3]) =
      some (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3) := by
  cases operator <;> simp [wordExpToInstruction, registerOfNat]

theorem compileWordBinOp_sound [NeZero width] (state : State width)
    (operator : BinOp) :
    evalWordProg state
        (.assign 1 (.op operator [.var 2, .var 3])) =
      some (execute state (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3)) := by
  cases operator <;>
    simp [evalWordProg, evalWordExp, registerOfNat, execute,
      writeRegister, nextPc]

theorem compileWordAdd_zeroState [NeZero width] :
    evalWordProg (zeroState width)
        (.assign 1 (.const (7 : Word width))) =
      some (executeInstructions (zeroState width) [.addi 1 0 7]) := by
  simp [evalWordProg, evalWordExp, executeInstructions, registerOfNat,
    execute, writeRegister, nextPc, ZeroRegister, zeroState, readRegister]

theorem wordFunctionToRiscV_return_add [NeZero width] :
    wordFunctionToRiscV
        ((.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) :
          WordProg (Word width)) =
      some ([.add 1 2 3], [1]) := by
  simp [wordFunctionToRiscV, wordExpToInstruction, registerOfNat]

theorem evalWordFunction_return_add [NeZero width] (state : State width) :
    evalWordFunction state
        (.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) =
      some (execute state (.add 1 2 3),
        [readRegister (execute state (.add 1 2 3)) 1]) := by
  simp [evalWordFunction, evalWordExp, registerOfNat, execute,
    writeRegister, nextPc, readRegister]

def compileWordAdd [NeZero width] (destination left right : Nat) :
    Option (List (Instruction width)) :=
  wordProgToRiscV (.assign destination (.op .add [.var left, .var right]))

example [NeZero width] :
    compileWordAdd (width := width) 1 2 3 = some [.add 1 2 3] := by
  simp [compileWordAdd, wordProgToRiscV, wordExpToInstruction, registerOfNat]

example [NeZero width] :
    wordExpToInstruction (width := width) 1 (.op .xor [.var 2, .var 3]) =
      some (.xor 1 2 3) := by
  simp [wordExpToInstruction, registerOfNat]

end Flapjack.RiscV
