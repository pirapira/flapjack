import Flapjack.RiscV.Backend
import Flapjack.RiscV.CorrectnessBackend

/-!
Cake-faithful evaluator boundary for the straight-line Word fragment.

`evalWordProg` is the historical model evaluator: it lowers constants and
`LocValue` through the one-instruction boundary, which truncates wide values.
The executable pipeline never uses that path (it goes through the Lab
lowering), but theorem clients that want to reason about the checked Cake
selectors need an evaluator that lowers exactly like `wordProgToRiscVCake`.

This file defines that evaluator (`evalWordProgCake`) and proves the direct
analogue of `wordProgToRiscV_sound_of_straightLine` for the checked Cake
selector: if `wordProgToRiscVCake` accepts a straight-line program then
running the emitted instruction list from `state` is exactly what the
Cake-faithful evaluator computes.
-/

namespace Flapjack.RiscV

/-- Cake-faithful counterpart of `evalWordShareInst`: the address expression is
lowered through the checked Cake expression boundary rather than the historical
one-instruction selector. -/
def evalWordShareInstCake [NeZero width] (state : State width)
    (operator : WordMemOp) (name : Nat) (address : WordExp (Word width)) :
    Option (State width) := do
  let instructions ← wordShareInstToInstructionsCake operator name address
  pure (executeInstructions state instructions)

def evalWordProgCake [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width)
  | .skip => some state
  | .move _ moves => do
      let instructions ← wordMoveToInstructions moves
      pure (executeInstructions state instructions)
  | .assign name value => do
      let instructions ← wordExpToInstructionsCake name value
      pure (executeInstructions state instructions)
  | .tick => pure (execute state (.addi 0 0 0))
  | .inst (.const destination value) => do
      let instructions ← wordInstToInstructionsCake (.const destination value)
      pure (executeInstructions state instructions)
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (executeInstructions state instructions)
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address))
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address))
  | .inst (.mem .load16 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalf destination address))
  | .inst (.mem .store16 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalf source address))
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address))
  | .store address value =>
      evalWordShareInstCake state .store value address
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address))
  | .inst (.mem .store source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWord source address))
  | .inst (.mem .load destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWord destination address))
  | .inst (.memOffset .load destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWordOffset destination address offset))
  | .inst (.memOffset .load8 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByteOffset destination address offset))
  | .inst (.memOffset .load16 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalfOffset destination address offset))
  | .inst (.memOffset .load32 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32Offset destination address offset))
  | .inst (.memOffset .store source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWordOffset source address offset))
  | .inst (.memOffset .store8 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByteOffset source address offset))
  | .inst (.memOffset .store16 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalfOffset source address offset))
  | .inst (.memOffset .store32 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32Offset source address offset))
  | .shareInst operator name address =>
      evalWordShareInstCake state operator name address
  | .locValue destination source => do
      let instructions ← wordLocValueToInstructionsCake destination source 0
      pure (executeInstructions state instructions)
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordProgCake state thenBranch
      else evalWordProgCake state elseBranch
  | .mustTerminate body => evalWordProgCake state body
  | .seq first second => do
      let state ← evalWordProgCake state first
      evalWordProgCake state second
  | _ => none
  termination_by program => sizeOf program
  decreasing_by all_goals decreasing_trivial

theorem wordProgToRiscVCake_sound_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscVCake program = some code) :
    evalWordProgCake state program = some (executeInstructions state code) := by
  induction hstraight generalizing state code with
  | skip =>
      have hcompile' : some ([] : List (Instruction width)) = some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      have hcode : ([] : List (Instruction width)) = code :=
        Option.some.inj hcompile'
      subst code
      simp [evalWordProgCake, executeInstructions]
  | move store moves =>
      have hcompile' : wordMoveToInstructions (width := width) moves = some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      cases h : wordMoveToInstructions (width := width) moves with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProgCake, h]
  | assign destination value =>
      have hcompile' : wordExpToInstructionsCake (width := width) destination value = some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      cases h : wordExpToInstructionsCake (width := width) destination value with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProgCake, h]
  | inst instruction =>
      cases instruction with
      | arith operation =>
          have hcompile' : wordArithToInstructions (width := width) operation = some code := by
            simpa only [wordProgToRiscVCake, wordInstToInstructionsCake] using hcompile
          cases h : wordArithToInstructions (width := width) operation with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instructions =>
              have hcode : instructions = code :=
                Option.some.inj (h.symm.trans hcompile')
              subst code
              simp [evalWordProgCake, h]
      | const destination value =>
          have hcompile' : wordInstToInstructionsCake (width := width)
            (.const destination value) = some code := by
            simpa only [wordProgToRiscVCake] using hcompile
          cases h : wordInstToInstructionsCake (width := width)
              (.const destination value) with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instructions =>
              have hcode : instructions = code :=
                Option.some.inj (h.symm.trans hcompile')
              subst code
              simp [evalWordProgCake, h]
      | mem operator destination address =>
          have hcompile' : (wordInstToInstruction (width := width)
            (.mem operator destination address)).map List.singleton =
            some code := by
            simpa only [wordProgToRiscVCake, wordInstToInstructionsCake] using hcompile
          cases h : wordInstToInstruction (width := width)
              (.mem operator destination address) with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instruction =>
              have hcode : List.singleton instruction = code := by
                have hcompile'' : some (List.singleton instruction) = some code := by
                  simpa [h] using hcompile'
                exact Option.some.inj hcompile''
              subst code
              cases operator <;>
                cases hd : registerOfNat destination <;>
                cases ha : registerOfNat address <;>
                simp [wordInstToInstruction, hd, ha] at h
              all_goals
                simp [evalWordProgCake, List.singleton, hd, ha, h]
      | memOffset operator destination address offset =>
          have hcompile' : (wordInstToInstruction (width := width)
            (.memOffset operator destination address offset)).map
              List.singleton = some code := by
            simpa only [wordProgToRiscVCake, wordInstToInstructionsCake] using hcompile
          cases h : wordInstToInstruction (width := width)
              (.memOffset operator destination address offset) with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instruction =>
              have hcode : List.singleton instruction = code := by
                have hcompile'' : some (List.singleton instruction) = some code := by
                  simpa [h] using hcompile'
                exact Option.some.inj hcompile''
              subst code
              cases operator <;>
                cases hd : registerOfNat destination <;>
                cases ha : registerOfNat address <;>
                simp [wordInstToInstruction, hd, ha] at h
              all_goals
                simp [evalWordProgCake, List.singleton, hd, ha, h]
  | store address value =>
      have hcompile' : wordShareInstToInstructionsCake (width := width) .store value address =
          some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      cases h : wordShareInstToInstructionsCake (width := width) .store value address with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProgCake, evalWordShareInstCake, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [wordProgToRiscVCake] at hcompile
      cases hfirstCompile : wordProgToRiscVCake first with
      | none => simp [hfirstCompile] at hcompile
      | some firstCode =>
          cases hsecondCompile : wordProgToRiscVCake second with
          | none => simp [hsecondCompile] at hcompile
          | some secondCode =>
              have hfirst' := ihfirst state firstCode hfirstCompile
              have hsecond' := ihsecond
                (executeInstructions state firstCode) secondCode hsecondCompile
              have hcode : firstCode ++ secondCode = code := by
                simpa [hfirstCompile, hsecondCompile] using hcompile
              subst code
              simp [evalWordProgCake, hfirst', hsecond', executeInstructions_append]
  | locValue destination source =>
      have hcompile' : wordLocValueToInstructionsCake (width := width) destination source 0 =
          some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      cases h : wordLocValueToInstructionsCake (width := width) destination source 0 with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProgCake, h]
  | tick =>
      have hcompile' : some ([.addi 0 0 0] : List (Instruction width)) = some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      have hcode : ([.addi 0 0 0] : List (Instruction width)) = code :=
        Option.some.inj hcompile'
      subst code
      simp [evalWordProgCake, executeInstructions]
  | shareInst operator name address =>
      have hcompile' : wordShareInstToInstructionsCake (width := width) operator name address =
          some code := by
        simpa only [wordProgToRiscVCake] using hcompile
      cases h : wordShareInstToInstructionsCake (width := width) operator name address with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProgCake, evalWordShareInstCake, h]

/-! Focused regressions for the checked Cake evaluator boundary. -/

/-- The checked Cake evaluator agrees with running the emitted code on the
trivial straight-line program, exercising the new soundness theorem. -/
example (state : State 64) :
    evalWordProgCake state (.skip : WordProg (Word 64)) =
      some (executeInstructions state ([] : List (Instruction 64))) := by
  have hstraight : WordRiscVStraightLine (.skip : WordProg (Word 64)) := .skip
  have hcompile : wordProgToRiscVCake (.skip : WordProg (Word 64)) =
      some ([] : List (Instruction 64)) := by
    simp [wordProgToRiscVCake]
  exact wordProgToRiscVCake_sound_of_straightLine state _ hstraight _ hcompile

/-- The checked Cake evaluator lowers a `LocValue` through the position-aware
AUIPC+ADDI boundary rather than the historical single instruction. -/
example (state : State 64) :
    evalWordProgCake state (.locValue 4 0x1234 : WordProg (Word 64)) =
      some (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) 4 0x1234 0).getD [])) := by
  simp [evalWordProgCake, wordLocValueToInstructionsCake, registerOfNat]

end Flapjack.RiscV
