import Flapjack.Word
import Flapjack.RiscV.Model

/-!
The first executable Word-to-RISC-V instruction-selection slice.

This is intentionally a partial compiler. It covers the Word fragment made of
`skip`, assignments, sequencing, equality/order/bit-test conditionals,
constants, register reads, binary arithmetic, shifts, and selected memory
operations. Immediate-zero conditions use the architectural x0 register. Bit
tests reuse the condition register as the `AND` destination, so that register
is dead after the condition. The option-valued interface makes the current
boundary explicit while the remaining Word instructions are ported.
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
  | .shift operator (.var left) (.var right) => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      let right ← registerOfNat right
      match operator with
      | .lsl => pure (.sll destination left right)
      | .lsr => pure (.srl destination left right)
      | .asr => pure (.sra destination left right)
      | .ror => none
  | _ => none

def wordArithToInstruction [NeZero width] :
    WordArith → Option (Instruction width)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      if destinationLeft = destinationRight then do
        let destination ← registerOfNat destinationLeft
        let sourceLeft ← registerOfNat sourceLeft
        let sourceRight ← registerOfNat sourceRight
        pure (.mul destination sourceLeft sourceRight)
      else none
  | .longDiv _ _ _ _ _ | .div _ _ _ => none

def wordInstToInstruction [NeZero width] :
    WordInst → Option (Instruction width)
  | .arith operation => wordArithToInstruction operation
  | .mem .load8 destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.loadByte destination address)
  | .mem .store8 source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.storeByte source address)
  | .mem .load32 destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.load32 destination address)
  | .mem .store32 source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.store32 source address)
  | .mem .load destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.loadWord destination address)
  | .mem .store source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.storeWord source address)

def wordProgToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width))
  | .skip => some []
  | .assign name value =>
      (wordExpToInstruction name value).map (fun instruction => [instruction])
  | .store (.var address) value => do
      let value ← registerOfNat value
      let address ← registerOfNat address
      pure [.storeWord value address]
  | .inst instruction =>
      (wordInstToInstruction instruction).map (fun instruction => [instruction])
  | .seq first second => do
      let first ← wordProgToRiscV first
      let second ← wordProgToRiscV second
      pure (first ++ second)
  | .tick => some [.addi 0 0 0]
  | .ite operator condition rightValue thenBranch elseBranch => do
      let condition ← registerOfNat condition
      let right ← match rightValue with
        | .reg right => registerOfNat right
        | .imm value => if value == 0 then pure 0 else none
      let thenCode ← wordProgToRiscV thenBranch
      let elseCode ← wordProgToRiscV elseBranch
      let falseOffset : Word width :=
        BitVec.ofNat width (8 + 4 * thenCode.length)
      let endOffset : Word width :=
        BitVec.ofNat width (4 + 4 * elseCode.length)
      let branchFalse ← match operator with
        | .equal => pure (.branchNe condition right falseOffset)
        | .notEqual => pure (.branchEq condition right falseOffset)
        | .less => pure (.branchGe condition right falseOffset)
        | .notLess => pure (.branchLt condition right falseOffset)
        | .lower => pure (.branchGeU condition right falseOffset)
        | .notLower => pure (.branchLtU condition right falseOffset)
        | .test => pure (.branchNe condition 0 falseOffset)
        | .notTest => pure (.branchEq condition 0 falseOffset)
      let prelude := match operator with
        | .test | .notTest => [.and condition condition right]
        | _ => []
      pure (prelude ++ [branchFalse] ++ thenCode ++
        [.branchEq 0 0 endOffset] ++ elseCode)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def executeInstructions [NeZero width] (state : State width) :
    List (Instruction width) → State width
  | [] => state
  | instruction :: instructions =>
      executeInstructions (execute state instruction) instructions

/-!
`executeInstructions` is useful for straight-line code, but it deliberately
does not interpret branch targets.  This runner treats `start` as the address
of the first instruction and follows the architectural program counter.
Execution stops when the PC reaches the first byte after the code.
-/
def executeCode [NeZero width] :
    Nat → Word width → List (Instruction width) → State width → Option (State width)
  | 0, _, _, _ => none
  | fuel + 1, start, code, state =>
      let byteOffset := (state.pc - start).toNat
      if byteOffset % 4 ≠ 0 then none
      else
        let index := byteOffset / 4
        match code[index]? with
        | some instruction => executeCode fuel start code (execute state instruction)
        | none => if index = code.length then some state else none

theorem executeCode_conditional_equal :
    (executeCode 10 (0 : Word 32)
      [.branchNe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (zeroState 32)).map (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notEqual :
    (executeCode 10 (0 : Word 32)
      [.branchEq 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (zeroState 32) 1 9)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_lower :
    (executeCode 10 (0 : Word 32)
      [.branchGeU 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notLower :
    (executeCode 10 (0 : Word 32)
      [.branchLtU 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

theorem executeCode_conditional_less :
    (executeCode 10 (0 : Word 32)
      [.branchGe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 (BitVec.ofNat 32 (2 ^ 32 - 1))) 2 0)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notLess :
    (executeCode 10 (0 : Word 32)
      [.branchLt 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 (BitVec.ofNat 32 (2 ^ 32 - 1))) 2 0)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

theorem executeCode_conditional_test :
    (executeCode 12 (0 : Word 32)
      [.and 1 1 2, .branchNe 1 0 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notTest :
    (executeCode 12 (0 : Word 32)
      [.and 1 1 0, .branchEq 1 0 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (zeroState 32) 1 1)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

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
  | .shift operator (.var left) (.var right) => do
      let left ← registerOfNat left
      let right ← registerOfNat right
      match operator with
      | .lsl => pure (BitVec.shiftLeft (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .lsr => pure (BitVec.ushiftRight (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .asr => pure (BitVec.sshiftRight (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .ror => none
  | _ => none

def wordFunctionToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .skip => some ([], [])
  | .assign name value => do
      let instruction ← wordExpToInstruction name value
      pure ([instruction], [])
  | .inst instruction => do
      let instruction ← wordInstToInstruction instruction
      pure ([instruction], [])
  | .tick => pure ([.addi 0 0 0], [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let condition ← registerOfNat condition
      let right ← match rightValue with
        | .reg right => registerOfNat right
        | .imm value => if value == 0 then pure 0 else none
      let (thenCode, thenReturns) ← wordFunctionToRiscV thenBranch
      let (elseCode, elseReturns) ← wordFunctionToRiscV elseBranch
      if thenReturns != elseReturns then none
      else
        let falseOffset : Word width :=
          BitVec.ofNat width (8 + 4 * thenCode.length)
        let endOffset : Word width :=
          BitVec.ofNat width (4 + 4 * elseCode.length)
        let branchFalse ← match operator with
          | .equal => pure (.branchNe condition right falseOffset)
          | .notEqual => pure (.branchEq condition right falseOffset)
          | .less => pure (.branchGe condition right falseOffset)
          | .notLess => pure (.branchLt condition right falseOffset)
          | .lower => pure (.branchGeU condition right falseOffset)
          | .notLower => pure (.branchLtU condition right falseOffset)
          | .test => pure (.branchNe condition 0 falseOffset)
          | .notTest => pure (.branchEq condition 0 falseOffset)
        let prelude := match operator with
          | .test | .notTest => [.and condition condition right]
          | _ => []
        pure (prelude ++ [branchFalse] ++ thenCode ++
          [.branchEq 0 0 endOffset] ++ elseCode, thenReturns)
  | .seq first second => do
      let (firstCode, firstReturns) ← wordFunctionToRiscV first
      let (secondCode, secondReturns) ← wordFunctionToRiscV second
      pure (firstCode ++ secondCode,
        if secondReturns.isEmpty then firstReturns else secondReturns)
  | .return _ values => do
      let values ← values.mapM registerOfNat
      pure ([], values)
  | _ => none

def evalWordCondition [NeZero width] (state : State width)
    (operator : Cmp) (condition : Nat) (rightValue : WordRegImm (Word width)) :
    Option Bool := do
  let condition ← registerOfNat condition
  let left := readRegister state condition
  let right ← match rightValue with
    | .reg right => do
        let right ← registerOfNat right
        pure (readRegister state right)
    | .imm value => pure value
  match operator with
  | .equal => pure (left == right)
  | .notEqual => pure (left != right)
  | .less => pure (signedLess left right)
  | .notLess => pure (!signedLess left right)
  | .lower => pure (decide (left < right))
  | .notLower => pure (decide (¬ left < right))
  | .test => pure (left &&& right == 0)
  | .notTest => pure (left &&& right != 0)

def evalWordFunction [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width × List (Word width))
  | .skip => some (state, [])
  | .assign name value => do
      let destination ← registerOfNat name
      let value ← evalWordExp state value
      pure (writeRegister { state with pc := nextPc state } destination value, [])
  | .tick => pure (execute state (.addi 0 0 0), [])
  | .inst (.arith operation) => do
      let instruction ← wordArithToInstruction operation
      pure (execute state instruction, [])
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address), [])
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address), [])
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address), [])
  | .store (.var address) value => do
      let value ← registerOfNat value
      let address ← registerOfNat address
      pure (execute state (.storeWord value address), [])
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address), [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordFunction state thenBranch
      else evalWordFunction state elseBranch
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
  | .tick => pure (execute state (.addi 0 0 0))
  | .inst (.arith operation) => do
      let instruction ← wordArithToInstruction operation
      pure (execute state instruction)
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address))
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address))
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address))
  | .store (.var address) value => do
      let value ← registerOfNat value
      let address ← registerOfNat address
      pure (execute state (.storeWord value address))
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address))
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordProg state thenBranch
      else evalWordProg state elseBranch
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

theorem compileWordShiftLsl_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.var 3))) =
      some (execute state (.sll 1 2 3)) := by
  simp [evalWordProg, evalWordExp, registerOfNat, execute,
    writeRegister, nextPc, shiftAmount]

theorem compileWordShiftLsr_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.var 3))) =
      some (execute state (.srl 1 2 3)) := by
  simp [evalWordProg, evalWordExp, registerOfNat, execute,
    writeRegister, nextPc, shiftAmount]

theorem compileWordShiftAsr_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.var 3))) =
      some (execute state (.sra 1 2 3)) := by
  simp [evalWordProg, evalWordExp, registerOfNat, execute,
    writeRegister, nextPc, shiftAmount]

theorem compileWordAdd_zeroState [NeZero width] :
    evalWordProg (zeroState width)
        (.assign 1 (.const (7 : Word width))) =
      some (executeInstructions (zeroState width) [.addi 1 0 7]) := by
  simp [evalWordProg, evalWordExp, executeInstructions, registerOfNat,
    execute, writeRegister, nextPc, ZeroRegister, zeroState, readRegister]

theorem compileWordLoadByte_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .load8 1 2)) =
      some (execute state (.loadByte 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, writeByte,
    readByte, nextPc]

theorem compileWordStoreByte_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .store8 1 2)) =
      some (execute state (.storeByte 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, writeByte,
    readByte, nextPc]

theorem compileWordLoad32_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .load32 1 2)) =
      some (execute state (.load32 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, readWord32,
    readByte, byteAddress, nextPc]

theorem compileWordStore32_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .store32 1 2)) =
      some (execute state (.store32 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeWord32, writeByte,
    byteAddress, nextPc]

theorem compileWordStoreWord_sound [NeZero width] (state : State width) :
    evalWordProg state (.store (.var 2) 1) =
      some (execute state (.storeWord 1 2)) := by
  simp [evalWordProg, evalWordExp, registerOfNat, execute, writeWordValue,
    writeByte, byteAddress, nextPc]

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

theorem wordFunctionToRiscV_return_const [NeZero width] (value : Word width) :
    wordFunctionToRiscV
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (Word width)) =
      some ([.addi 1 0 value], [1]) := by
  simp [wordFunctionToRiscV, wordExpToInstruction, registerOfNat]

theorem evalWordFunction_return_const [NeZero width] (state : State width)
    (value : Word width) (zero : ZeroRegister state) :
    evalWordFunction state
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (Word width)) =
      some (execute state (.addi 1 0 value),
        [readRegister (execute state (.addi 1 0 value)) 1]) := by
  simp [evalWordFunction, evalWordExp, registerOfNat, execute,
    writeRegister, nextPc, readRegister]
  constructor
  · funext current
    by_cases h : current = 1
    · subst current
      simpa [ZeroRegister, readRegister] using zero
    · simp [h]
  · simpa [ZeroRegister, readRegister] using zero

theorem wordArithToInstruction_longMul [NeZero width] :
    wordArithToInstruction (width := width) (.longMul 1 1 2 3) =
      some (.mul 1 2 3) := by
  simp [wordArithToInstruction, registerOfNat]

theorem compileWordLongMul_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.arith (.longMul 1 1 2 3))) =
      some (execute state (.mul 1 2 3)) := by
  simp [evalWordProg, wordArithToInstruction, registerOfNat]

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

example [NeZero width] :
    wordInstToInstruction (width := width) (.arith (.longMul 1 1 2 3)) =
      some (.mul 1 2 3) := by
  simp [wordInstToInstruction, wordArithToInstruction, registerOfNat]

end Flapjack.RiscV
