import Flapjack.RiscV.Backend
import Flapjack.RiscV.CakeSoundness
import Flapjack.RiscV.Calls
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Encoding
import Flapjack.RiscV.Lab
import Flapjack.RiscV.LocValue

/-! Direct CakeML `riscv_ast (Inst (Const ...))` oracle checks.

`wordExpToInstruction` remains the theorem-facing one-instruction API.  These
checks cover the separate constants boundary, whose list shape follows
`riscv_targetScript.sml` (`riscv_ast_def` and `riscv_const32_def`). -/

namespace Flapjack.RiscV

/-! Cake's signed-12 immediate path includes the zero boundary: even the
    architectural zero is materialized as the explicit `ORI rd, x0, 0` in
    `riscv_ast`, rather than being silently dropped. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0) =
      some [.ori 4 0 (BitVec.ofNat 64 0)] := by
  decide

/- The same Cake boundary is preserved by the executable Lab materializer. -/
example :
    labConstInstructions (width := 64) 4 0 31 0 =
      [.ori 4 0 (BitVec.ofNat 64 0)] := by
  decide

example :
    labConstInstructions (width := 64) 4 0 31 (2 ^ 64 - 1) =
      [.ori 4 0 (BitVec.ofNat 64 0xfff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12) =
      some [.ori 4 0 (BitVec.ofNat 64 0x12)] := by
  decide

/-! Signed-12 endpoints from Cake's `valid_imm`/`riscv_ast` boundary. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2047) =
      some [.ori 4 0 (BitVec.ofNat 64 0x7ff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 2048)) =
      some [.ori 4 0 (BitVec.ofNat 64 0x800)] := by
  decide

/-! The negative signed-12 endpoint is still a direct `ORI`; the positive
    value with the same low 12 bits is not sign-extended and therefore takes
    Cake's two-instruction `riscv_const32` path. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 1)) =
      some [.ori 4 0 (BitVec.ofNat 64 0xfff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 4095 =
      some [.lui 4 (BitVec.ofNat 64 (2 ^ 20 - 1)),
        .xori 4 4 (BitVec.ofNat 64 0xfff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12345678) =
      some [.lui 4 (BitVec.ofNat 64 0x12345),
        .addi 4 4 (BitVec.ofNat 64 0x678)] := by
  decide

/-! A negative signed-32 constant takes Cake's `riscv_const32` path too:
    the sign-extended RV64 value keeps the low word and materializes it with
    `LUI`/`ADDI`, rather than falling through to the wide two-word sequence. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 31)) =
      some [.lui 4 (BitVec.ofNat 64 0x80000),
        .addi 4 4 (BitVec.ofNat 64 0)] := by
  decide

/-! The positive signed-32 endpoint uses Cake's sign-bit `XORI` form:
    `LUI 0x80000` followed by `XORI -1` materializes `0x7fffffff`. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 31 - 1)) =
      some [.lui 4 (BitVec.ofNat 64 0x80000),
        .xori 4 4 (BitVec.ofNat 64 0xfff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) =
      some [.lui 31 (BitVec.ofNat 64 0x55667),
        .addi 31 31 (BitVec.ofNat 64 0x788),
        .lui 4 (BitVec.ofNat 64 0x11223),
        .addi 4 4 (BitVec.ofNat 64 0x344),
        .slli 4 4 (BitVec.ofNat 64 32),
        .or 4 4 31] := by
  decide

/-! Negative wide values use the Cake high-word complement and XOR carrier. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0xffeeddccbbaa9988) =
      some [.lui 31 (BitVec.ofNat 64 0x44556),
        .xori 31 31 (BitVec.ofNat 64 0x988),
        .lui 4 (BitVec.ofNat 64 0x112),
        .addi 4 4 (BitVec.ofNat 64 0x233),
        .slli 4 4 (BitVec.ofNat 64 32),
        .xor 4 4 31] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 (2 ^ 64 - 8)) =
      some [.ori 4 0 (BitVec.ofNat 64 0xff8)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2048) =
      some [.lui 4 (BitVec.ofNat 64 0xfffff),
        .xori 4 4 (BitVec.ofNat 64 0x800)] := by
  decide

/- The checked expression boundary routes constants through the Cake list
   lowering while preserving the old selector for all other expressions. -/
example :
    wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1234)) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  decide

example :
    wordExpToInstructionsCake (width := 64) 4
        (.load (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234),
        .loadWord 4 31] := by
  decide

example :
    wordProgToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordProgToRiscVCake (width := 64)
        (.inst (.const 4 (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordInstToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVCake (width := 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVCake,
    wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

/-! Executable obligations for the Cake-faithful multi-instruction boundary.

These deliberately exercise the emitted instruction list, rather than the
legacy one-instruction expression API. -/
theorem cakeConst1234_execution_oracle :
    (wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1234) := by
  decide

theorem cakeConstWide_execution_oracle :
    (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1122334455667788) := by
  decide

/-! The signed-12 endpoints are executable Cake materialization boundaries,
    not merely instruction-list shape checks. -/
theorem cakeConst2047_execution_oracle :
    (wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2047)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 2047) := by
  decide

theorem cakeConstNeg2048_execution_oracle :
    (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 2048))).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 (2 ^ 64 - 2048)) := by
  decide

/-! The expression-facing Cake boundary preserves the same executable
    obligations while leaving the historical one-instruction selector intact.
    These are theorem-facing API checks, not production-caller migration. -/
theorem cakeExp1234_execution_oracle :
    (wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1234))).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1234) := by
  decide

theorem cakeExpWide_execution_oracle :
    (wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1122334455667788))).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1122334455667788) := by
  decide

/-! The call-aware Cake boundary preserves the return carrier while allowing a
wide assignment to materialize as the complete Cake instruction list.  The
legacy call-aware selector remains unchanged so its existing correctness
contract continues to use the historical one-instruction API. -/
example :
    wordFunctionToRiscVWithCallsCake (width := 64)
        ({ targets := [] } : WordCallContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
        (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVWithCallsCake (width := 64)
        ({ targets := [] } : WordCallContext 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788))) =
      (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
          (fun instructions => (instructions, [])) := by
  exact wordFunctionToRiscVWithCallsCake_const _ 4
    (BitVec.ofNat 64 0x1122334455667788)

/-! Cake's list-valued constant boundary composes with both call carriers.
These are direct source-shaped sequences: the constant is fully materialized
before the parameter move, and the ordinary call retains Cake's saved-link and
return-move protocol. -/
example :
    wordFunctionToRiscVWithCallsCake (width := 64)
        ({ targets := [(7, BitVec.ofNat 64 32, [2], [10])] } : WordCallContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234),
        .addi 2 6 0,
        .addi 30 30 (0 - BitVec.ofNat 64 8),
        .storeWord 1 30,
        .addi 31 0 (BitVec.ofNat 64 32),
        .jalr 1 31 0,
        .addi 4 10 0,
        .loadWord 1 30,
        .addi 30 30 (BitVec.ofNat 64 8)], []) := by
  simp [wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions,
    wordCallToRiscVWithStack, wordRegisterMoves, lookupWordCallTarget,
    registerOfNat]

example :
    wordFunctionToRiscVWithCallsCake (width := 64)
        ({ targets := [(7, BitVec.ofNat 64 32, [2], [10])] } : WordCallContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.call none (some 7) [6] none)) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234),
        .addi 2 6 0,
        .addi 31 0 (BitVec.ofNat 64 32),
        .jalr 0 31 0], [10]) := by
  simp [wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions,
    wordTailCallToRiscV, wordRegisterMoves, lookupWordCallTarget,
    registerOfNat]

/-! A wide constant used as a memory address keeps Cake's complete address
    materialization before the final store carrier. -/
example :
    wordShareInstToInstructionsCake (width := 64) .store 4
        (.const (BitVec.ofNat 64 0x1234)) =
      some ([.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234), .storeWord 4 31]) := by
  rw [wordShareInstToInstructionsCake_const]
  simp [wordConstToInstructions, wordConst32ToInstructions, wordInstToInstruction,
    registerOfNat]

/-! The FFI-aware Cake boundary preserves the same multi-instruction constant
    materialization and return carrier while retaining its service table. -/
example :
    wordFunctionToRiscVWithCallsAndFfiCake (width := 64)
        ({ targets := [], services := [] } : WordCallFfiContext 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1234))) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake,
    wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVWithCallsAndFfiCake (width := 64)
        ({ targets := [], services := [] } : WordCallFfiContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake,
    wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVWithCallsAndFfiCake (width := 64)
        ({ targets := [], services := [] } : WordCallFfiContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788)))
          (.return 0 [4])) =
      (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
          (fun instructions => (instructions, [4])) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake,
    wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

/- The FFI-aware wrapper preserves the same Cake call carriers when a
   list-valued constant precedes an ordinary or tail call. -/
example :
    wordFunctionToRiscVWithCallsAndFfiCake (width := 64)
        ({ targets := [(7, BitVec.ofNat 64 32, [2], [10])], services := [] } :
          WordCallFfiContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234),
        .addi 2 6 0,
        .addi 30 30 (0 - BitVec.ofNat 64 8),
        .storeWord 1 30,
        .addi 31 0 (BitVec.ofNat 64 32),
        .jalr 1 31 0,
        .addi 4 10 0,
        .loadWord 1 30,
        .addi 30 30 (BitVec.ofNat 64 8)], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake,
    wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions,
    wordCallToRiscVWithStack, wordRegisterMoves, lookupWordCallTarget,
    registerOfNat]

example :
    wordFunctionToRiscVWithCallsAndFfiCake (width := 64)
        ({ targets := [(7, BitVec.ofNat 64 32, [2], [10])], services := [] } :
          WordCallFfiContext 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.call none (some 7) [6] none)) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234),
        .addi 2 6 0,
        .addi 31 0 (BitVec.ofNat 64 32),
        .jalr 0 31 0], [10]) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake,
    wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions,
    wordTailCallToRiscV, wordRegisterMoves, lookupWordCallTarget,
    registerOfNat]

example (state : State 64) :
    evalWordProgCake state
        (.assign 4 (.const (BitVec.ofNat 64 0x1234)) : WordProg (Word 64)) =
      some (executeInstructions state
        [.lui 4 (BitVec.ofNat 64 1),
         .addi 4 4 (BitVec.ofNat 64 0x234)]) := by
  simp [evalWordProgCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example (state : State 64) :
    evalWordProgCake state
        (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788)) :
          WordProg (Word 64)) =
      some (executeInstructions state
        ((wordConstToInstructions (width := 64) 4
          (BitVec.ofNat 64 0x1122334455667788)).getD [])) := by
  simp [evalWordProgCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example (state : State 64) :
    evalWordProgCake state
        (.assign 4 (.load (.const (BitVec.ofNat 64 0x1234))) :
          WordProg (Word 64)) =
      some (executeInstructions state
        [.lui 31 (BitVec.ofNat 64 1),
         .addi 31 31 (BitVec.ofNat 64 0x234),
         .loadWord 4 31]) := by
  simp [evalWordProgCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example (state : State 64) :
    evalWordFunctionCake state
        (.assign 4 (.const (BitVec.ofNat 64 0x1234)) : WordProg (Word 64)) =
      some (executeInstructions state
        [.lui 4 (BitVec.ofNat 64 1),
         .addi 4 4 (BitVec.ofNat 64 0x234)], []) := by
  have hstraight : WordRiscVStraightLine
      (.assign 4 (.const (BitVec.ofNat 64 0x1234)) : WordProg (Word 64)) :=
    .assign _ _
  have hcompile : wordFunctionToRiscVCake
      (.assign 4 (.const (BitVec.ofNat 64 0x1234)) : WordProg (Word 64)) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], []) := by
    simp [wordFunctionToRiscVCake, wordExpToInstructionsCake,
      wordConstToInstructions, wordConst32ToInstructions, registerOfNat]
  exact wordFunctionToRiscVCake_sound_of_straightLine state _ hstraight _ hcompile

example (state : State 64) :
    evalWordFunctionCake state
        (.assign 4 (.load (.const (BitVec.ofNat 64 0x1234))) :
          WordProg (Word 64)) =
      some (executeInstructions state
        [.lui 31 (BitVec.ofNat 64 1),
         .addi 31 31 (BitVec.ofNat 64 0x234),
         .loadWord 4 31], []) := by
  have hstraight : WordRiscVStraightLine
      (.assign 4 (.load (.const (BitVec.ofNat 64 0x1234))) :
        WordProg (Word 64)) := .assign _ _
  have hcompile : wordFunctionToRiscVCake
      (.assign 4 (.load (.const (BitVec.ofNat 64 0x1234))) :
        WordProg (Word 64)) =
      some ([.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234),
        .loadWord 4 31], []) := by
    simp [wordFunctionToRiscVCake, wordExpToInstructionsCake,
      wordConstToInstructions, wordConst32ToInstructions, registerOfNat]
  exact wordFunctionToRiscVCake_sound_of_straightLine state _ hstraight _ hcompile

example (state : State 64) :
    evalWordFunctionCake state
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4]) : WordProg (Word 64)) =
      some
        (executeInstructions state
          [.lui 4 (BitVec.ofNat 64 1),
           .addi 4 4 (BitVec.ofNat 64 0x234)],
         [readRegister
           (executeInstructions state
             [.lui 4 (BitVec.ofNat 64 1),
              .addi 4 4 (BitVec.ofNat 64 0x234)]) 4]) := by
  simp [evalWordFunctionCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

example (state : State 64) :
    evalWordFunctionCake state
        (.assign 4 (.const (BitVec.ofNat 64 0x1234)) : WordProg (Word 64)) =
      some (executeInstructions state
        [.lui 4 (BitVec.ofNat 64 1),
         .addi 4 4 (BitVec.ofNat 64 0x234)], []) := by
  simp [evalWordFunctionCake, wordExpToInstructionsCake,
    wordConstToInstructions, wordConst32ToInstructions, registerOfNat]

/-! The checked call-aware selector now has the same compositional theorem
    shape as the legacy theorem-facing selector.  This exercises the sequence
    induction while retaining the full Cake list-valued constant boundary. -/
example :
    wordFunctionToRiscVWithCallsCake (width := 64)
        ({ targets := [] } : WordCallContext 64)
        (.seq
          (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788)))
          (.assign 5 (.var 4))) =
      (wordProgToRiscVCake (width := 64)
          (.seq
            (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788)))
            (.assign 5 (.var 4)))).map (fun code => (code, [])) := by
  exact wordFunctionToRiscVWithCallsCake_agrees_cakeStraightLine _ _
    (WordRiscVStraightLine.seq _ _
      (WordRiscVStraightLine.assign _ _)
      (WordRiscVStraightLine.assign _ _))

/-! `wordExpToInstruction` is not Cake-faithful for constants outside the
signed 12-bit immediate range: it returns a single `addi` whose immediate the
encoder silently truncates, while `wordConstToInstructions` emits the
`lui`/`addi` (or wider) sequence of `riscv_targetScript.sml:96`.  The witness
below records the information loss so callers that need the Cake shape use the
`wordConstToInstructions` boundary. -/

example :
    wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234)) =
      some (.addi 4 0 (BitVec.ofNat 64 0x1234)) := by
  decide

example :
    encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x1234)) =
      encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234)) := by
  decide

example :
    (wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234))).map
        (fun instruction => encodeInstruction instruction) =
      some (encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234))) := by
  decide

/-! ## Bridge to the executable Lab lowering

`labConst32` is the port of Cake's `riscv_const32`
(`riscv_targetScript.sml:77`) and `labConstInstructions` is the port of the
`Const` clause of `riscv_ast_def` (`riscv_targetScript.sml:96`).  The
`wordConst*` definitions are the option-valued, checked theorem boundary.  The
theorems below show that the two boundaries emit exactly the same instruction
lists, so correctness statements about `wordConstToInstructions` transfer to
the executable pipeline. -/

theorem wordConst32ToInstructions_eq_labConst32 {width : Nat} [NeZero width] :
    (wordConst32ToInstructions (width := width)) =
      (labConst32 (width := width)) := by
  rfl

private theorem some_ite {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (some (if c then a else b) : Option α) = if c then some a else some b := by
  split <;> rfl

theorem wordConstToInstructions_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordConstToInstructions (width := width) destination value =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) := by
  unfold wordConstToInstructions labConstInstructions
  simp only [registerOfNat, hdestination]
  rw [wordConst32ToInstructions_eq_labConst32]
  have hmod : value.toNat % 2 ^ width = value.toNat :=
    Nat.mod_eq_of_lt value.isLt
  by_cases hsmall : value.toNat < 2 ^ 11
  · have hlow : value.toNat % 2 ^ 12 = value.toNat :=
      Nat.mod_eq_of_lt (by omega)
    simp [hsmall, hlow]
  · simp only [hsmall, if_false, hmod]
    by_cases hfit :
        (value.toNat ==
          (if value.toNat % 2 ^ 12 / 2 ^ 11 % 2 = 0 then value.toNat % 2 ^ 12
            else (2 ^ width - (2 ^ 12 - value.toNat % 2 ^ 12)) % 2 ^ width)) =
          true
    · simp [hfit]
    · simp only [hfit]
      simp only [some_ite]
      simp

/-- The expression-facing Cake boundary selects the checked constant lowering
for `.const`, so it agrees with the executable Lab materialization while the
legacy one-instruction selector stays unchanged. -/
theorem wordExpToInstructionsCake_const_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordExpToInstructionsCake (width := width) destination (.const value) =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) :=
  wordConstToInstructions_eq_labConstInstructions destination value hdestination

/-! The instruction-facing Cake boundary selects the same checked constant
    lowering as the expression-facing boundary. -/
theorem wordInstToInstructionsCake_const_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordInstToInstructionsCake (width := width) (.const destination value) =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) :=
  by simpa [wordInstToInstructionsCake_const] using
    (wordConstToInstructions_eq_labConstInstructions destination value hdestination)

/-! The function-level checked boundary composes the same Cake constant list
    with its return carrier.  This is the reusable migration theorem for
    callers that currently depend on the legacy one-instruction selector. -/
theorem wordFunctionToRiscVCake_const_assign_return_eq_labConstInstructions
    {width : Nat} [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordFunctionToRiscVCake (width := width)
        (.seq (.assign destination (.const value))
          (.return 0 [destination])) =
      some
        (labConstInstructions (width := width) ⟨destination, hdestination⟩
            0 31 value.toNat,
          [⟨destination, hdestination⟩]) := by
  simp [wordFunctionToRiscVCake, wordExpToInstructionsCake,
    registerOfNat, hdestination,
    wordConstToInstructions_eq_labConstInstructions destination value
      hdestination]

/-- The 0x1234 materialization oracle through the expression-facing Cake
boundary, stated directly against the executable Lab lowering. -/
example :
    wordExpToInstructionsCake (width := 64) 4 (.const (BitVec.ofNat 64 0x1234)) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

example :
    wordInstToInstructionsCake (width := 64)
        (.const 4 (BitVec.ofNat 64 0x1234)) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

/-! A constant used as a load address must retain the complete Cake
materialization before the load; this is the recursive expression boundary,
not the legacy one-instruction selector. -/
example :
    wordExpToInstructionsCake (width := 64) 1
        (.load (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234),
        .loadWord 1 31] := by
  decide

/-- The 0x1234 materialization oracle, stated directly against the executable
Lab lowering rather than only against `wordConstToInstructions`. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

/-- The wide-constant materialization oracle against the executable Lab
lowering. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) =
      some (labConstInstructions (width := 64) 4 0 31 0x1122334455667788) := by
  decide

/-! ## LocValue boundary witness (bead flapjack-pxn.1.4)

The standalone Word selector now uses the same position-zero `auipc`/`addi`
pair as Cake's `riscv_ast (Loc r i)` and the executable Lab selector.  These
checks keep the public boundary and its instruction count aligned with the
original backend shape. -/

example :
    wordLocValueToInstructions (width := 64) 4 0x1234 =
      some (labLocValueInstructions (width := 64) 4 0x1234 0) := by
  decide

example :
    (wordLocValueToInstructions (width := 64) 4 0x1234).map List.length =
      some 2 := by
  decide

example :
    (labLocValueInstructions (width := 64) 4 0x1234 0).length = 2 := by
  decide

/-! ### Checked Cake-faithful LocValue boundary (bead flapjack-pxn.1.4)

`wordLocValueToInstructionsCake` is the position-aware `AUIPC`/`ADDI` boundary
that mirrors Cake's `riscv_ast (Loc r i)`.  The bridge below proves it emits
exactly the instructions of the executable Lab selector, so a theorem client
can use the checked boundary while the pipeline keeps using `labLocValueInstructions`. -/

example :
    wordLocValueToInstructionsCake (width := 64) 4 0x1234 0 =
      some (labLocValueInstructions (width := 64) 4 0x1234 0) := by
  decide

example :
    (wordLocValueToInstructionsCake (width := 64) 4 0x1234 0).map List.length =
      some 2 := by
  decide

example :
    wordLocValueToInstructionsCake (width := 64) 4 0x123456 0x1000 =
      some (labLocValueInstructions (width := 64) 4 0x123456 0x1000) := by
  decide

/-- Executing the checked Cake-faithful `LocValue` boundary materializes the
label value, mirroring the constant execution oracles: the `auipc`/`addi`
pair computes `label - position` relative to the current program counter. -/
example :
    readRegister
        (executeInstructions (zeroState 64)
          (labLocValueInstructions (width := 64) 4 0x1234 0)) 4 =
      some (BitVec.ofNat 64 0x1234) := by
  decide

/-! Focused regressions for the same checked boundary across the offset shapes
that the `auipc`/`addi` split must handle: an aligned upward delta, an aligned
downward page crossing, a negative delta whose signed 12-bit remainder forces a
carry, a wide label spread over many pages, and an unaligned program counter.
The `auipc`/`addi` pair computes `label - position + position`. -/
example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0 }
          (labLocValueInstructions (width := 64) 4 0x2000 0)) 4 =
      BitVec.ofNat 64 0x2000 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0 0x1000)) 4 =
      BitVec.ofNat 64 0 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x800 0x1000)) 4 =
      BitVec.ofNat 64 0x800 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x123456 0x1000)) 4 =
      BitVec.ofNat 64 0x123456 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 2 }
          (labLocValueInstructions (width := 64) 4 0x1004 2)) 4 =
      BitVec.ofNat 64 0x1004 := by
  decide

example :
    wordProgToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordProgToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788))) =
      wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) := by
  exact wordProgToRiscVCake_const 4 (BitVec.ofNat 64 0x1122334455667788)

example :
    wordProgToRiscVCake (width := 64)
        (.inst (.const 4 (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordInstToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVCake (width := 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVCake,
    wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1122334455667788))) =
      (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
          (fun instructions => (instructions, [])) := by
  exact wordFunctionToRiscVCake_const 4 (BitVec.ofNat 64 0x1122334455667788)

def cakeConstFunctionExecution : Option (List (Word 64)) :=
  (wordFunctionToRiscVCake (width := 64)
    (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
      (.return 0 [4]))).map fun (code, returns) =>
    returns.map (readRegister (executeInstructions (zeroState 64) code))

#guard cakeConstFunctionExecution = some [BitVec.ofNat 64 0x1234]

/-! The checked `...Cake` program and function boundaries now route `locValue`
through the position-aware Cake-faithful lowering (default position `0` for the
non-layout API), so they emit the `auipc`/`addi` pair rather than a single
truncating `addi`. -/
example :
    wordProgToRiscVCake (width := 64) (.locValue 4 0x1234) =
      some [.auipc 4 (BitVec.ofInt 64 1),
        .addi 4 4 (BitVec.ofInt 64 0x234)] := by
  simp [wordProgToRiscVCake, wordLocValueToInstructionsCake, registerOfNat]

example :
    wordProgToRiscVCake (width := 64) (.locValue 4 0x1234) =
      some (labLocValueInstructions (width := 64) 4 0x1234 0) := by
  simp [wordProgToRiscVCake, wordLocValueToInstructionsCake,
    labLocValueInstructions, registerOfNat]

example :
    (wordFunctionToRiscVCake (width := 64) (.locValue 4 0x1234)).map Prod.fst =
      some (labLocValueInstructions (width := 64) 4 0x1234 0) := by
  simp [wordFunctionToRiscVCake, wordLocValueToInstructionsCake,
    labLocValueInstructions, registerOfNat]

/-! Focused regressions for the same checked boundary across the offset shapes
that the `auipc`/`addi` split must handle: an aligned upward delta, an aligned
downward page crossing, a negative delta whose signed 12-bit remainder forces a
carry, a wide label spread over many pages, and an unaligned program counter.
The `auipc`/`addi` pair computes `label - position + position`. -/
example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0 }
          (labLocValueInstructions (width := 64) 4 0x2000 0)) 4 =
      BitVec.ofNat 64 0x2000 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0 0x1000)) 4 =
      BitVec.ofNat 64 0 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x800 0x1000)) 4 =
      BitVec.ofNat 64 0x800 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x123456 0x1000)) 4 =
      BitVec.ofNat 64 0x123456 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 2 }
          (labLocValueInstructions (width := 64) 4 0x1004 2)) 4 =
      BitVec.ofNat 64 0x1004 := by
  decide


end Flapjack.RiscV
