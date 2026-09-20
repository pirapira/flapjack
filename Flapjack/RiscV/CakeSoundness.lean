import Flapjack.RiscV.Backend
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Ffi

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

/-!
## Function-level Cake-faithful evaluator

`evalWordFunction` is the historical function-level evaluator; it carries the
ABI return list alongside the resulting machine state.  This section defines the
Cake-faithful counterpart `evalWordFunctionCake` (same clauses, checked Cake
lowering) and lifts the straight-line soundness result from the program level to
the function level.  Source, memory and FFI-relevant state stay explicit: the
evaluator takes `state` and returns the resulting `State` together with the
returned registers.
-/

/-- Cake-faithful counterpart of `evalWordFunction`: identical clause structure,
but constants, shared-instruction addresses and `LocValue` go through the
checked Cake selectors. -/
def evalWordFunctionCake [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width × List (Word width))
  | .skip => some (state, [])
  | .move _ moves => do
      let instructions ← wordMoveToInstructions moves
      pure (executeInstructions state instructions, [])
  | .assign name value => do
      let instructions ← wordExpToInstructionsCake name value
      pure (executeInstructions state instructions, [])
  | .tick => pure (execute state (.addi 0 0 0), [])
  | .inst (.const destination value) => do
      let instructions ← wordInstToInstructionsCake (.const destination value)
      pure (executeInstructions state instructions, [])
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (executeInstructions state instructions, [])
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address), [])
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address), [])
  | .inst (.mem .load16 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalf destination address), [])
  | .inst (.mem .store16 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalf source address), [])
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address), [])
  | .store address value => do
      let state ← evalWordShareInstCake state .store value address
      pure (state, [])
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address), [])
  | .inst (.mem .store source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWord source address), [])
  | .inst (.mem .load destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWord destination address), [])
  | .inst (.memOffset .load destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWordOffset destination address offset), [])
  | .inst (.memOffset .load8 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByteOffset destination address offset), [])
  | .inst (.memOffset .load16 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalfOffset destination address offset), [])
  | .inst (.memOffset .load32 destination address offset) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32Offset destination address offset), [])
  | .inst (.memOffset .store source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWordOffset source address offset), [])
  | .inst (.memOffset .store8 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByteOffset source address offset), [])
  | .inst (.memOffset .store16 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalfOffset source address offset), [])
  | .inst (.memOffset .store32 source address offset) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32Offset source address offset), [])
  | .shareInst operator name address => do
      let state ← evalWordShareInstCake state operator name address
      pure (state, [])
  | .locValue destination source => do
      let instructions ← wordLocValueToInstructionsCake destination source 0
      pure (executeInstructions state instructions, [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordFunctionCake state thenBranch
      else evalWordFunctionCake state elseBranch
  | .mustTerminate body => evalWordFunctionCake state body
  | .seq first second => do
      let (state, firstReturns) ← evalWordFunctionCake state first
      if !firstReturns.isEmpty then
        pure (state, firstReturns)
      else
        let (state, secondReturns) ← evalWordFunctionCake state second
        pure (state, secondReturns)
  | .return _ values => do
      let values ← values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister state register))
      pure (state, values)
  | _ => none
  termination_by program => sizeOf program
  decreasing_by all_goals decreasing_trivial

/-- On the straight-line fragment the function-level Cake evaluator is the
program-level Cake evaluator paired with the empty return carrier. -/
theorem evalWordFunctionCake_wordRiscVStraightLine_eq_evalWordProgCake [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    evalWordFunctionCake state program =
      (evalWordProgCake state program).map (fun state => (state, [])) := by
  induction hstraight generalizing state with
  | skip => simp [evalWordFunctionCake, evalWordProgCake]
  | move store moves => simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
  | assign destination value =>
      simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
  | inst instruction =>
      cases instruction with
      | arith operation =>
          simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
      | const destination value =>
          simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
      | mem operator destination address =>
          cases operator <;>
            simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
      | memOffset operator destination address offset =>
          cases operator <;>
            simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
  | store address value =>
      cases h : wordShareInstToInstructionsCake (width := width) .store value address <;>
        simp [evalWordFunctionCake, evalWordProgCake, evalWordShareInstCake, h]
  | locValue destination source =>
      simp [evalWordFunctionCake, evalWordProgCake, Function.comp_def]
  | tick => simp [evalWordFunctionCake, evalWordProgCake]
  | shareInst operator name address =>
      cases h : wordShareInstToInstructionsCake (width := width) operator name address <;>
        simp [evalWordFunctionCake, evalWordProgCake, evalWordShareInstCake, h]
  | @seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [evalWordFunctionCake, evalWordProgCake]
      rw [ihfirst state]
      cases hfirstEval : evalWordProgCake state first with
      | none => simp
      | some firstState =>
          simp [ihsecond firstState]
          cases hsecondEval : evalWordProgCake firstState second with
          | none => simp
          | some secondState => simp

/-- The function-level Cake selector omits the `.move` clause (mirroring the
historical `wordFunctionToRiscV`), so on straight-line programs it accepts only
programs without `move`.  On those programs it agrees with the program-level
Cake selector, and its return carrier is always empty. -/
theorem wordFunctionToRiscVCake_code_eq_wordProgToRiscVCake_of_straightLine
    [NeZero width] (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width)) (returns : List (Fin 32))
    (hcompile : wordFunctionToRiscVCake program = some (code, returns)) :
    wordProgToRiscVCake program = some code ∧ returns = [] := by
  induction hstraight generalizing code returns with
  | skip =>
      simpa [wordFunctionToRiscVCake, wordProgToRiscVCake] using hcompile
  | move store moves =>
      simp [wordFunctionToRiscVCake] at hcompile
  | assign destination value =>
      cases h : wordExpToInstructionsCake (width := width) destination value with
      | none => simp [wordFunctionToRiscVCake, h] at hcompile
      | some instructions =>
          simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, h] using hcompile
  | inst instruction =>
      cases h : wordInstToInstructionsCake (width := width) instruction with
      | none => simp [wordFunctionToRiscVCake, h] at hcompile
      | some instructions =>
          simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, h] using hcompile
  | store address value =>
      cases h : wordShareInstToInstructionsCake (width := width) .store value address with
      | none => simp [wordFunctionToRiscVCake, h] at hcompile
      | some instructions =>
          simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, h] using hcompile
  | shareInst operator name address =>
      cases h : wordShareInstToInstructionsCake (width := width) operator name address with
      | none => simp [wordFunctionToRiscVCake, h] at hcompile
      | some instructions =>
          simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, h] using hcompile
  | locValue destination source =>
      cases h : wordLocValueToInstructionsCake (width := width) destination source 0 with
      | none => simp [wordFunctionToRiscVCake, h] at hcompile
      | some instructions =>
          simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, h] using hcompile
  | tick =>
      simpa [wordFunctionToRiscVCake, wordProgToRiscVCake] using hcompile
  | seq first second hfirst hsecond ihfirst ihsecond =>
      cases hfirstCompile : wordFunctionToRiscVCake first with
      | none => simp [wordFunctionToRiscVCake, hfirstCompile] at hcompile
      | some firstResult =>
          obtain ⟨firstCode, firstReturns⟩ := firstResult
          obtain ⟨hfirstProg, hfirstReturns⟩ :=
            ihfirst firstCode firstReturns hfirstCompile
          subst firstReturns
          cases hsecondCompile : wordFunctionToRiscVCake second with
          | none =>
              simp [wordFunctionToRiscVCake, hfirstCompile, hsecondCompile]
                at hcompile
          | some secondResult =>
              obtain ⟨secondCode, secondReturns⟩ := secondResult
              obtain ⟨hsecondProg, hsecondReturns⟩ :=
                ihsecond secondCode secondReturns hsecondCompile
              subst secondReturns
              simpa [wordFunctionToRiscVCake, wordProgToRiscVCake, hfirstCompile,
                hsecondCompile, hfirstProg, hsecondProg] using hcompile

/-- Function-level Cake-faithful soundness for the straight-line fragment: if the
checked Cake function selector accepts a straight-line program then running the
emitted instructions is exactly the Cake-faithful evaluator, with an empty
return carrier. -/
theorem wordFunctionToRiscVCake_sound_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVCake program = some (code, [])) :
    evalWordFunctionCake state program =
      some (executeInstructions state code, []) := by
  obtain ⟨hbase, _⟩ :=
    wordFunctionToRiscVCake_code_eq_wordProgToRiscVCake_of_straightLine
      program hstraight code [] hcompile
  have hword := wordProgToRiscVCake_sound_of_straightLine state program
    hstraight code hbase
  rw [evalWordFunctionCake_wordRiscVStraightLine_eq_evalWordProgCake state
    program hstraight, hword]
  rfl

/-!
The call-aware Cake selector accepts `.move`, which the bare function selector
rejects, so its soundness theorem is the one that covers the move fragment of
the straight-line API.  It composes the Cake agreement bridge with the
program-level Cake soundness theorem and the function/program evaluator
equivalence proved above.
-/

theorem wordFunctionToRiscVWithCallsCake_sound_of_straightLine [NeZero width]
    (context : WordCallContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCallsCake context program =
      some (code, [])) :
    evalWordFunctionCake state program =
      some (executeInstructions state code, []) := by
  have hagree := wordFunctionToRiscVWithCallsCake_agrees_cakeStraightLine
    context program hstraight
  rw [hagree] at hcompile
  have hbase : wordProgToRiscVCake program = some code := by
    cases hcode : wordProgToRiscVCake program with
    | none => simp [hcode] at hcompile
    | some instructions =>
        have hinstructions : instructions = code := by
          simpa [hcode] using hcompile
        exact congrArg (fun xs : List (Instruction width) => some xs) hinstructions
  have hword := wordProgToRiscVCake_sound_of_straightLine state program
    hstraight code hbase
  rw [evalWordFunctionCake_wordRiscVStraightLine_eq_evalWordProgCake state
    program hstraight, hword]
  rfl

/-! Focused regressions for the function-level Cake boundary. -/

/-- The call-aware Cake selector accepts an empty `.move`, so the call-aware
soundness theorem covers the move fragment that the function selector rejects. -/
example (context : WordCallContext 64) (state : State 64) :
    evalWordFunctionCake state (.move 0 [] : WordProg (Word 64)) =
      some (executeInstructions state ([] : List (Instruction 64)),
        ([] : List (Word 64))) := by
  have hstraight : WordRiscVStraightLine (.move 0 [] : WordProg (Word 64)) :=
    .move 0 []
  have hcompile : wordFunctionToRiscVWithCallsCake context
      (.move 0 [] : WordProg (Word 64)) =
      some (([] : List (Instruction 64)), ([] : List (Fin 32))) := by
    simp [wordFunctionToRiscVWithCallsCake, wordMoveToInstructions,
      wordMoveToInstructionsAux, wordMoveRegisterDestinations]
  exact wordFunctionToRiscVWithCallsCake_sound_of_straightLine context state
    _ hstraight _ hcompile

/-- Function-level soundness exercised on the trivial straight-line program. -/
example (state : State 64) :
    evalWordFunctionCake state (.skip : WordProg (Word 64)) =
      some (executeInstructions state ([] : List (Instruction 64)),
        ([] : List (Word 64))) := by
  have hstraight : WordRiscVStraightLine (.skip : WordProg (Word 64)) := .skip
  have hcompile : wordFunctionToRiscVCake (.skip : WordProg (Word 64)) =
      some (([] : List (Instruction 64)), ([] : List (Fin 32))) := by
    simp [wordFunctionToRiscVCake]
  exact wordFunctionToRiscVCake_sound_of_straightLine state _ hstraight _ hcompile

/-- The function-level Cake selector keeps the multi-instruction AUIPC+ADDI
materialization of `LocValue` visible. -/
example :
    wordFunctionToRiscVCake (.locValue 4 0x1234 : WordProg (Word 64)) =
      some ([.auipc 4 (BitVec.ofInt 64 1), .addi 4 4 (BitVec.ofInt 64 0x234)],
        ([] : List (Fin 32))) := by
  simp [wordFunctionToRiscVCake, wordLocValueToInstructionsCake, registerOfNat]

/-!
The FFI/call-aware evaluator keeps the source state, memory, and handler
visible in its arguments.  On the straight-line fragment it agrees with the
plain evaluator; the explicit fuel premise accounts for nested sequences.
-/

theorem option_bind_pair_eta {α β : Type} (x : Option (α × β)) :
    x.bind (fun p => some (p.1, p.2)) = x := by
  cases x <;> rfl

theorem evalWordFunctionWithCallsAndFfi_straightLine_eq_evalWordFunction
    {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (fuel : Nat) (hfuel : sizeOf program + 1 ≤ fuel) :
    evalWordFunctionWithCallsAndFfi functions handler fuel state program =
      evalWordFunction state program := by
  induction hstraight generalizing state fuel with
  | skip => cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | move store moves =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | assign destination value =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | inst instruction =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | store address value =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | locValue destination source =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | tick => cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | shareInst operator name address =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      cases fuel with
      | zero => omega
      | succ k =>
          have hk : sizeOf first + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          have hk2 : sizeOf second + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          simp only [evalWordFunctionWithCallsAndFfi, evalWordFunction]
          rw [ihfirst state k hk]
          rw [evalWordFunction_wordRiscVStraightLine_eq_evalWordProg state first hfirst]
          cases heval : evalWordProg state first with
          | none => simp
          | some firstState =>
              simp [ihsecond firstState k hk2, option_bind_pair_eta]

/-- The FFI-aware evaluator agrees with the plain evaluator on a straight-line
skip when the fuel exceeds the program size. -/
example (functions : List (Nat × List Nat × WordProg (Word 64)))
    (handler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
      State 64 → Option (State 64)) (state : State 64) :
    evalWordFunctionWithCallsAndFfi functions handler
        (sizeOf (.skip : WordProg (Word 64)) + 1) state
        (.skip : WordProg (Word 64)) =
      evalWordFunction state (.skip : WordProg (Word 64)) :=
  evalWordFunctionWithCallsAndFfi_straightLine_eq_evalWordFunction functions
    handler state (.skip : WordProg (Word 64)) .skip _ (Nat.le_refl _)

/-!
The handler-aware control evaluator `evalWordFunctionWithHandlersAndFfi`
returns a `WordControlResult` and keeps the function table, FFI handler, and
source state visible.  On the straight-line fragment no call, FFI action,
raise, or return can occur, so it must coincide with the plain evaluator,
wrapped into `.normal`.  The explicit fuel premise again accounts for nested
sequences.
-/

theorem option_bind_normal_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    (evalWordFunction state program).bind
      (fun p => if p.2.isEmpty then some (WordControlResult.normal p.1)
                else some (WordControlResult.returned p.1 p.2)) =
    (evalWordProg state program).map (fun state => WordControlResult.normal state) := by
  rw [evalWordFunction_wordRiscVStraightLine_eq_evalWordProg state program hstraight]
  cases evalWordProg state program <;> simp

theorem evalWordFunctionWithHandlersAndFfi_straightLine_eq_evalWordProg_normal
    {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (ffiHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (fuel : Nat) (hfuel : sizeOf program + 1 ≤ fuel) :
    evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel state program =
      (evalWordProg state program).map (fun state => WordControlResult.normal state) := by
  induction hstraight generalizing state fuel with
  | skip =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.skip : WordProg (Word width)) .skip
  | move store moves =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.move store moves) (.move store moves)
  | assign destination value =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.assign destination value)
            (.assign destination value)
  | inst instruction =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.inst instruction) (.inst instruction)
  | store address value =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.store address value)
            (.store address value)
  | locValue destination source =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.locValue destination source)
            (.locValue destination source)
  | tick =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.tick : WordProg (Word width)) .tick
  | shareInst operator name address =>
      cases fuel with
      | zero => omega
      | succ k =>
          simp only [evalWordFunctionWithHandlersAndFfi]
          exact option_bind_normal_of_straightLine state (.shareInst operator name address)
            (.shareInst operator name address)
  | @seq first second hfirst hsecond ihfirst ihsecond =>
      cases fuel with
      | zero => omega
      | succ k =>
          have hk : sizeOf first + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          have hk2 : sizeOf second + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          simp only [evalWordFunctionWithHandlersAndFfi, evalWordProg]
          rw [ihfirst state k hk]
          cases heval : evalWordProg state first with
          | none => simp
          | some firstState => simp [ihsecond firstState k hk2]

/-- Regression: the handler-aware evaluator returns `.normal` on a straight-line
skip once the fuel exceeds the program size. -/
example (functions : List (Nat × List Nat × WordProg (Word 64)))
    (ffiHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
      State 64 → Option (State 64)) (state : State 64) :
    evalWordFunctionWithHandlersAndFfi functions ffiHandler
        (sizeOf (.skip : WordProg (Word 64)) + 1) state
        (.skip : WordProg (Word 64)) =
      some (WordControlResult.normal state) := by
  rw [evalWordFunctionWithHandlersAndFfi_straightLine_eq_evalWordProg_normal functions
    ffiHandler state (.skip : WordProg (Word 64)) .skip _ (Nat.le_refl _)]
  simp [evalWordProg]

end Flapjack.RiscV
